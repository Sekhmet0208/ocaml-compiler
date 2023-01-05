module Syntax = struct
  type expr =
    | Int of { value : int; pos : Lexing.position }
    | Bool of { value : bool; pos : Lexing.position }
    | Var of { name : string; pos : Lexing.position }
    | Call of { func : string; args : expr list; pos : Lexing.position }

  type type_t = Bool_t | Int_t | Func_t of type_t * type_t list

  type instr =
    | DeclVar of { name : string; pos : Lexing.position }
    | Assign of { var : string; expr : expr; pos : Lexing.position }
    | Return of { expr : expr; pos : Lexing.position }
    | Cond of {
        cond : expr;
        then_block : block;
        else_block : block;
        pos : Lexing.position;
      }
    | Loop of { cond : expr; block : block; pos : Lexing.position }

  and block = instr list
end

module IR = struct
  type expr =
    | Int of int
    | Bool of bool
    | Var of string
    | Call of string * expr list

  type instr =
    | DeclVar of string
    | Assign of string * expr
    | Return of expr
    | Cond of expr * block * block
    | Loop of expr * block

  and block = instr list
end
