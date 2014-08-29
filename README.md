Cobalt
======

COnstraint-BAsed Little Typechecker

## Syntax

```
program := data* import* defn*
data    := "data" dataname tyvar* ";"
import  := "import" termvar "::" polytype ";"
defn    := termvar "=" expr "=>" okfail ";"
         | termvar "::" polytype "=" expr "=>" okfail ";"
okfail  := "ok" | "fail"

polytype := "{" tyvar ">" polytype "}" polytype
          | "{" tyvar "=" polytype "}" polytype
		  | "{" tyvar "}" polytype
		  | monotype
		  | "_|_"
monotype := tyvar
          | dataname monotype*
		  | monotype "->" monotype
		  | "[" monotype "]"
		  | "(" monotype "," monotype ")"
		  | "(" monotype ")"
dataname := "'" identifier

expr := intliteral
      | termvar
	  | "\" termvar "->" expr
	  | "\" termvar "::" polytype "->" expr
	  | expr expr
	  | "let" termvar "=" expr "in" expr
	  | "let" termvar "::" polytype "=" expr "in" expr
	  | "match" expr "with" dataname alt*
alt  := "|" termvar termvar* "->" expr
```
