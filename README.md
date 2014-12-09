Cobalt
======

**Cobalt** is an acronym for COnstraint-BAsed Little Typechecker. In its core, it is an implementation of [OutsideIn](http://research.microsoft.com/en-us/um/people/simonpj/papers/constraints/jfp-outsidein.pdf), the type checking and inference engine used in the [GHC](https://www.haskell.org/ghc/) Haskell compiler since version 7. Apart from the solver itself, it contains two implementations of constraint gathering:

  * [A more traditional one](https://github.com/serras/cobalt/blob/master/src/Cobalt/OutsideIn/Gather.hs), which merely traverses the tree, and which implementes the original algorithm found in the [paper](http://research.microsoft.com/en-us/um/people/simonpj/papers/constraints/jfp-outsidein.pdf).
  * [An extensible implementation](https://github.com/serras/cobalt/blob/master/src/Cobalt/Script/Gather.hs) based on the [`t-regex`](https://github.com/serras/t-regex) package, which is expressed as an attribute grammar, and which supports specialized type rules.


## Syntax

```
program := (data | axiom | import | defn)*
data    := "data" dataname tyvar* ";"
import  := "import" termvar "::" polytype ";"
defn    := termvar termvar* ("::" polytype)? "=" expr ("=>" okfail)? ";"
okfail  := "ok" | "fail"

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

axiom := "axiom" ("{" tyvar "}")* monotype "~" monotype ";"
       | "axiom" ("{" tyvar "}")* constraint* "=>" clsname monotype* ";"

expr := intliteral
      | termvar
	  | "\" termvar "->" expr
	  | "\" termvar "::" polytype "->" expr
	  | expr expr
	  | "let" termvar "=" expr "in" expr
	  | "let" termvar "::" polytype "=" expr "in" expr
	  | "match" expr "with" dataname alt*
alt  := "|" termvar termvar* "->" expr

dataname := "'" identifier
famname  := "^" identifier
clsname  := "$" identifier
```
