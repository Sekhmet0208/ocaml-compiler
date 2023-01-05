
(* The type of tokens. *)

type token = 
  | Lwhile
  | Lvar
  | Ltrue of (bool)
  | Lthen
  | Lsub
  | Lsc
  | Lreturn
  | LopenP
  | Lmul
  | Lint of (int)
  | Lif
  | Lident of (string)
  | Lfalse of (bool)
  | Lequal
  | Leq
  | Lend
  | Lelse
  | Ldo
  | Ldiv
  | LcloseP
  | Ladd
  | LNequal

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.Syntax.block)
