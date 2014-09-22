Cobalt
======

COnstraint-BAsed Little Typechecker

## Syntax

```
program := data* import* axiom* defn*
data    := "data" dataname tyvar* ";"
import  := "import" termvar "::" polytype ";"
defn    := termvar ("::" polytype)? "=" expr ("=>" okfail)? ";"
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
