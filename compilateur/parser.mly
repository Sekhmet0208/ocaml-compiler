%{
  open Ast.Syntax
%}
%token LopenP
%token LcloseP
%token <int> Lint
%token <bool> Ltrue
%token <bool> Lfalse
%token <string> Lident
%token Lif
%token Lelse
%token Lthen
%token Lwhile
%token Ldo

%token Lsc Lend Lvar Leq Lreturn Lmul Ladd Lsub Ldiv LNequal Lequal




%start prog


%type <Ast.Syntax.block> prog


%%
block:
| i = instr ; Lsc ; b = block { i @ b }
| i = instr ; Lsc { i }
;



prog:
	| i = instr ; Lsc ; b = prog { i @ b }
	| i = instr ; Lsc ; Lend { i }
;

instr:
  | Lvar; id = Lident 
  {
   [ DeclVar { name = id ; pos = $startpos(id)}]
  }
  | Lvar; id = Lident; Leq; e = expr
  {
    [ DeclVar { name = id ; pos = $startpos(id)}
      ; Assign { var = id ; expr = e ; pos = $startpos($3) }
    ]
  }
  | id = Lident; Leq; e = expr
  {
	[ Assign { var = id
     		 ; expr = e 
    		 ; pos = $startpos($2) 
    		 }
    ]
  }
  | Lreturn; e = expr { [ Return { expr = e; pos = $startpos($1) } ] }
  | Lif; c = expr; Lthen; t = block; Lelse; e = block
    {
        [ Cond { cond = c; then_block = t; else_block = e; pos = $startpos(c) } ]
    }
  | Lwhile; c = expr; Ldo; b = block
    {
    [ Loop { cond = c; block = b; pos = $startpos(c) } ]
    }



expr:
| n = Lint {
  Int { value = n ; pos = $startpos(n) }
}
| b = Ltrue  { Bool { value = b ; pos = $startpos(b)} }
| b = Lfalse { Bool { value = b ; pos = $startpos(b)} }
| v = Lident { Var { name = v ; pos = $startpos(v)} }

| left = expr; Lmul; right = expr{ 
  Call { func = "_mul"
       ; args = [left ; right ]
       ; pos = $startpos($2) }
}
| left = expr; Ladd; right = expr{
  Call { func = "_add"
       ; args = [left ; right ]
       ; pos = $startpos($2) }
}

| left = expr; Lsub; right = expr{
  Call { func = "_sub"
       ; args = [left ; right ]
       ; pos = $startpos($2) }
}

| left = expr; Ldiv; right = expr{
  Call { func = "_div"
       ; args = [left ; right ]
       ; pos = $startpos($2) }
}

| left = expr; Lequal; right = expr{
  Call { func = "_equal"
       ; args = [left ; right ]
       ; pos = $startpos($2) }
}


| left = expr; LNequal; right = expr{
  Call { func = "_neq"
       ; args = [left ; right ]
       ; pos = $startpos($2) }
}
| LopenP ; e = expr; LcloseP{e}
;
