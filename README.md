Cobalt
======

**Cobalt** is an acronym for COnstraint-BAsed Little Typechecker. In its core, it is an implementation of [OutsideIn](http://research.microsoft.com/en-us/um/people/simonpj/papers/constraints/jfp-outsidein.pdf), the type checking and inference engine used in the [GHC](https://www.haskell.org/ghc/) Haskell compiler since version 7, with extra support for higher-ranked types. Apart from the solver itself, it contains two implementations of constraint gathering:

  * [A more traditional one](https://github.com/serras/cobalt/blob/master/src/Cobalt/OutsideIn/Gather.hs), which merely traverses the tree, and which implementes the original algorithm found in the [OutsideIn paper](http://research.microsoft.com/en-us/um/people/simonpj/papers/constraints/jfp-outsidein.pdf).
  * [An extensible implementation](https://github.com/serras/cobalt/blob/master/src/Cobalt/Script/Gather.hs) based on the [`t-regex`](https://github.com/serras/t-regex) package, which is expressed as an attribute grammar, and which supports specialized type rules.

## Running

Cobalt comes with a *web interface* which you can use to typecheck a program, but also to inspect the gathered constraints and the solving process. The easiest way to get the interface is by running

```
stack run c -- serve p
```

where `c` can be either `cobalt` (for using traditional gathering) or `cobalt-u` (for using the extensible implementation). On the other hand `p` must be a number, which is the port in which the web interface will listed. Then, just point your browser to `http://localhost:p` :)

You might also load some predefined examples via the corresponding buttons. Most of them highlight either parts of the syntax or some of the Cobalt specific features, such as specialized type rules or higher-ranked types.

## Syntax

In essence, Cobalt is just a typed lambda calculus with pattern matching, plus a language of constraints and axioms in the type level. Given that the main aim of Cobalt is studying type systems, the syntax for expressions those is quite rich:

```
polytype   := "{" tyvar "}" polytype
            | constraint* "=>" monotype
monotype   := tyvar
            | dataname monotype*
            | famname monotype*
            | monotype "->" monotype
            | "[" monotype "]"
            | "(" monotype "," monotype ")"
            | "(" monotype ")"
constraint := monotype ">" polytype
            | monotype "=" polytype
            | monotype "~" monotype
            | clsname monotype*

dataname := "'" identifier
famname  := "^" identifier
clsname  := "$" identifier
```

Note that, in order to keep the ideas as clear as possible, type constructors **must** be tagged with their sort by a one-symbol prefix. Data constructors such as `'Int` or `'Bool` have a quote at the beginning. Type families (which also include type synonyms) needs a caret in front of them `^F^. Finally, type classes are indicated by a dollar sign, such as `$Eq` or `$Functor`.

Another change with respect to Haskell is that you **must** always annotate which variables are bound in a polymorphic data type. These bindings are indicated by `{v}`, where `v` is the variable you bind upon. For example, the type of `==` should be written as `{a} $Eq a => a -> a -> 'Bool`.

A program is made by a list of data, axiom, imports and definitions:

```
program := (data | axiom | import | defn)*
```

A **definition** is the specification of a value or function, and follows the syntax:

```
defn := termvar termvar* ("::" polytype)? "=" expr ("=>" okfail)? ";"

expr := intliteral
      | termvar
	  | "\" termvar "->" expr
	  | "\" termvar "::" polytype "->" expr
	  | expr expr
	  | "let" termvar "=" expr "in" expr
	  | "let" termvar "::" polytype "=" expr "in" expr
	  | "match" expr "with" dataname alt*
alt  := "|" termvar termvar* "->" expr

okfail := "ok" | "fail"
```

The main changes from Haskell syntax are:

  * Definitions must be terminated with semicolon `;`.
  * If you need to give an explicit type to an expression, you write this in-line with the definition instead of in a separate type signature. For example, you write `f :: 'Int = 3 + 5;`.
  * Instead of `case e of`, in Cobalt you use `match e with 'type`. The extra piece of information given by `type` keeps the gathering process much easier. Of course, in an actual implementation of a real language, `type` would be inferred from the context.
  * At the end of the definition, you might include an annotation `=> ok` or `=> fail` indicating whether type checking this expression should succeed or fail. This information is used in the graphical interface to indicate expected outcome.

When you want to give an environment to the type checker without actual expressions, you can **import** functions, which can later be used freely. Doing so is very easy, you just need to write `import`, the name and the type:

```
import := "import" termvar "::" polytype ";"
```

**Data types** in Cobalt are modelled in a special way. Instead of using an ADT-style declaration like in Haskell, their definition is split in two parts:

```
data := "data" dataname tyvar* ";"
```

  * A `data` declaration brings the new type into scope and gives the number and name of type parameters. For example, `data 'Maybe a;`.
  * Constructors are declared simply as other functions, using `import`. It is very important that the result type of the constructor has the same number of argumenrs as declared in `data`. For example `import Just :: {a} a -> 'Maybe a`.

Finally, we have **axioms** which define relations between constraints:

```
axiom := "axiom" ("{" tyvar "}")* monotype "~" monotype ";"
       | "axiom" ("{" tyvar "}")* constraint* "=>" clsname monotype* ";"
	   | "axiom" "injective" famname ";"
	   | "axiom" "defer" famname ";"
	   | "axiom" "synonym" ("{" tyvar "}")* monotype "~" monotype ";"
```

There are four main kinds of axioms in Cobalt:

  * *Unification axioms* model rewriting for type families and type synonyms. For example: `axiom {a} ^F a ~ 'Int`.
  * *Instance axioms* are used to declare based or derived instances of type classes. For example, the well-known instances for equality on integers and equality on lists are axiomatized as `axiom $Eq 'Int` and `axiom $Eq a => $Eq [a]`, respectively. Note that, being worried only on the typing part of the system, we do not give any function declaration in instances.
  * *Injectivity axioms* declare that for a given type family `^F`, we can derive equality of components from equality of the type family. That is, if `^F` has two parameters, from `^F a b ~ ^F c d` we can derive `a ~ c` and `b ~ d`.
  * *Deferral axioms* also apply to type families, and makes the solver wait as much as possible before rewriting the type family. This is very useful to model type synonyms, where we want the original type to remain as far as possible.

From those basic blocks, we can describe two derived forms of axioms:

  * Cobalt does not include support for general type application: you always need to head everything by a data type name or a type family name. However, you can model general application `x y` via a type `'App` and use merely `'App x y` instead. For example, here is the type of the monad bind function: `bind :: {m} {r} r > {a} {b} 'App m a -> (a -> 'App m b) -> 'App m b => 'Monad m -> r`.
  * Type synonyms are modelled as injective and deferred type families. However, you can summarize the three needed declarations in a single `axiom synonym` one.

## Specialized type rules

TODO
