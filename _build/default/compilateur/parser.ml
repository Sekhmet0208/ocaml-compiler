
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | Lwhile
    | Lvar
    | Ltrue of (
# 7 "compilateur/parser.mly"
       (bool)
# 17 "compilateur/parser.ml"
  )
    | Lthen
    | Lsub
    | Lsc
    | Lreturn
    | LopenP
    | Lmul
    | Lint of (
# 6 "compilateur/parser.mly"
       (int)
# 28 "compilateur/parser.ml"
  )
    | Lif
    | Lident of (
# 9 "compilateur/parser.mly"
       (string)
# 34 "compilateur/parser.ml"
  )
    | Lfalse of (
# 8 "compilateur/parser.mly"
       (bool)
# 39 "compilateur/parser.ml"
  )
    | Lequal
    | Leq
    | Lend
    | Lelse
    | Ldo
    | Ldiv
    | LcloseP
    | Ladd
    | LNequal
  
end

include MenhirBasics

# 1 "compilateur/parser.mly"
  
  open Ast.Syntax

# 59 "compilateur/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_prog) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: prog. *)

  | MenhirState01 : (('s, _menhir_box_prog) _menhir_cell1_Lwhile, _menhir_box_prog) _menhir_state
    (** State 01.
        Stack shape : Lwhile.
        Start symbol: prog. *)

  | MenhirState03 : (('s, _menhir_box_prog) _menhir_cell1_LopenP, _menhir_box_prog) _menhir_state
    (** State 03.
        Stack shape : LopenP.
        Start symbol: prog. *)

  | MenhirState08 : (('s, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Lsub, _menhir_box_prog) _menhir_state
    (** State 08.
        Stack shape : expr Lsub.
        Start symbol: prog. *)

  | MenhirState10 : (('s, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Lmul, _menhir_box_prog) _menhir_state
    (** State 10.
        Stack shape : expr Lmul.
        Start symbol: prog. *)

  | MenhirState12 : (('s, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Lequal, _menhir_box_prog) _menhir_state
    (** State 12.
        Stack shape : expr Lequal.
        Start symbol: prog. *)

  | MenhirState14 : (('s, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Ldiv, _menhir_box_prog) _menhir_state
    (** State 14.
        Stack shape : expr Ldiv.
        Start symbol: prog. *)

  | MenhirState16 : (('s, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Ladd, _menhir_box_prog) _menhir_state
    (** State 16.
        Stack shape : expr Ladd.
        Start symbol: prog. *)

  | MenhirState18 : (('s, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_LNequal, _menhir_box_prog) _menhir_state
    (** State 18.
        Stack shape : expr LNequal.
        Start symbol: prog. *)

  | MenhirState22 : ((('s, _menhir_box_prog) _menhir_cell1_Lwhile, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 22.
        Stack shape : Lwhile expr.
        Start symbol: prog. *)

  | MenhirState25 : (('s, _menhir_box_prog) _menhir_cell1_Lvar _menhir_cell0_Lident _menhir_cell0_Leq, _menhir_box_prog) _menhir_state
    (** State 25.
        Stack shape : Lvar Lident Leq.
        Start symbol: prog. *)

  | MenhirState27 : (('s, _menhir_box_prog) _menhir_cell1_Lreturn, _menhir_box_prog) _menhir_state
    (** State 27.
        Stack shape : Lreturn.
        Start symbol: prog. *)

  | MenhirState29 : (('s, _menhir_box_prog) _menhir_cell1_Lif, _menhir_box_prog) _menhir_state
    (** State 29.
        Stack shape : Lif.
        Start symbol: prog. *)

  | MenhirState31 : ((('s, _menhir_box_prog) _menhir_cell1_Lif, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 31.
        Stack shape : Lif expr.
        Start symbol: prog. *)

  | MenhirState33 : (('s, _menhir_box_prog) _menhir_cell1_Lident _menhir_cell0_Leq, _menhir_box_prog) _menhir_state
    (** State 33.
        Stack shape : Lident Leq.
        Start symbol: prog. *)

  | MenhirState36 : (('s, _menhir_box_prog) _menhir_cell1_instr, _menhir_box_prog) _menhir_state
    (** State 36.
        Stack shape : instr.
        Start symbol: prog. *)

  | MenhirState39 : (((('s, _menhir_box_prog) _menhir_cell1_Lif, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_block, _menhir_box_prog) _menhir_state
    (** State 39.
        Stack shape : Lif expr block.
        Start symbol: prog. *)

  | MenhirState44 : (('s, _menhir_box_prog) _menhir_cell1_instr, _menhir_box_prog) _menhir_state
    (** State 44.
        Stack shape : instr.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_block = 
  | MenhirCell1_block of 's * ('s, 'r) _menhir_state * (Ast.Syntax.block)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.Syntax.expr) * Lexing.position

and ('s, 'r) _menhir_cell1_instr = 
  | MenhirCell1_instr of 's * ('s, 'r) _menhir_state * (Ast.Syntax.block)

and 's _menhir_cell0_LNequal = 
  | MenhirCell0_LNequal of 's * Lexing.position

and 's _menhir_cell0_Ladd = 
  | MenhirCell0_Ladd of 's * Lexing.position

and 's _menhir_cell0_Ldiv = 
  | MenhirCell0_Ldiv of 's * Lexing.position

and 's _menhir_cell0_Leq = 
  | MenhirCell0_Leq of 's * Lexing.position

and 's _menhir_cell0_Lequal = 
  | MenhirCell0_Lequal of 's * Lexing.position

and ('s, 'r) _menhir_cell1_Lident = 
  | MenhirCell1_Lident of 's * ('s, 'r) _menhir_state * (
# 9 "compilateur/parser.mly"
       (string)
# 181 "compilateur/parser.ml"
) * Lexing.position

and 's _menhir_cell0_Lident = 
  | MenhirCell0_Lident of 's * (
# 9 "compilateur/parser.mly"
       (string)
# 188 "compilateur/parser.ml"
) * Lexing.position

and ('s, 'r) _menhir_cell1_Lif = 
  | MenhirCell1_Lif of 's * ('s, 'r) _menhir_state

and 's _menhir_cell0_Lmul = 
  | MenhirCell0_Lmul of 's * Lexing.position

and ('s, 'r) _menhir_cell1_LopenP = 
  | MenhirCell1_LopenP of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_Lreturn = 
  | MenhirCell1_Lreturn of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_Lsub = 
  | MenhirCell0_Lsub of 's * Lexing.position

and ('s, 'r) _menhir_cell1_Lvar = 
  | MenhirCell1_Lvar of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_Lwhile = 
  | MenhirCell1_Lwhile of 's * ('s, 'r) _menhir_state

and _menhir_box_prog = 
  | MenhirBox_prog of (Ast.Syntax.block) [@@unboxed]

let _menhir_action_01 =
  fun b i ->
    (
# 29 "compilateur/parser.mly"
                              ( i @ b )
# 220 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_02 =
  fun i ->
    (
# 30 "compilateur/parser.mly"
                  ( i )
# 228 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_03 =
  fun _startpos_n_ n ->
    (
# 72 "compilateur/parser.mly"
           (
  Int { value = n ; pos = _startpos_n_ }
)
# 238 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_04 =
  fun _startpos_b_ b ->
    (
# 75 "compilateur/parser.mly"
             ( Bool { value = b ; pos = _startpos_b_} )
# 246 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_05 =
  fun _startpos_b_ b ->
    (
# 76 "compilateur/parser.mly"
             ( Bool { value = b ; pos = _startpos_b_} )
# 254 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_06 =
  fun _startpos_v_ v ->
    (
# 77 "compilateur/parser.mly"
             ( Var { name = v ; pos = _startpos_v_} )
# 262 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_07 =
  fun _startpos__2_ left right ->
    (
# 79 "compilateur/parser.mly"
                                 ( 
  Call { func = "_mul"
       ; args = [left ; right ]
       ; pos = _startpos__2_ }
)
# 274 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_08 =
  fun _startpos__2_ left right ->
    (
# 84 "compilateur/parser.mly"
                                 (
  Call { func = "_add"
       ; args = [left ; right ]
       ; pos = _startpos__2_ }
)
# 286 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_09 =
  fun _startpos__2_ left right ->
    (
# 90 "compilateur/parser.mly"
                                 (
  Call { func = "_sub"
       ; args = [left ; right ]
       ; pos = _startpos__2_ }
)
# 298 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_10 =
  fun _startpos__2_ left right ->
    (
# 96 "compilateur/parser.mly"
                                 (
  Call { func = "_div"
       ; args = [left ; right ]
       ; pos = _startpos__2_ }
)
# 310 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_11 =
  fun _startpos__2_ left right ->
    (
# 102 "compilateur/parser.mly"
                                   (
  Call { func = "_equal"
       ; args = [left ; right ]
       ; pos = _startpos__2_ }
)
# 322 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_12 =
  fun _startpos__2_ left right ->
    (
# 109 "compilateur/parser.mly"
                                    (
  Call { func = "_neq"
       ; args = [left ; right ]
       ; pos = _startpos__2_ }
)
# 334 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_13 =
  fun e ->
    (
# 114 "compilateur/parser.mly"
                            (e)
# 342 "compilateur/parser.ml"
     : (Ast.Syntax.expr))

let _menhir_action_14 =
  fun _startpos_id_ id ->
    (
# 42 "compilateur/parser.mly"
  (
   [ DeclVar { name = id ; pos = _startpos_id_}]
  )
# 352 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_15 =
  fun _startpos__3_ _startpos_id_ e id ->
    (
# 46 "compilateur/parser.mly"
  (
    [ DeclVar { name = id ; pos = _startpos_id_}
      ; Assign { var = id ; expr = e ; pos = _startpos__3_ }
    ]
  )
# 364 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_16 =
  fun _startpos__2_ e id ->
    (
# 52 "compilateur/parser.mly"
  (
	[ Assign { var = id
     		 ; expr = e 
    		 ; pos = _startpos__2_ 
    		 }
    ]
  )
# 378 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_17 =
  fun _startpos__1_ e ->
    (
# 59 "compilateur/parser.mly"
                      ( [ Return { expr = e; pos = _startpos__1_ } ] )
# 386 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_18 =
  fun _startpos_c_ c e t ->
    (
# 61 "compilateur/parser.mly"
    (
        [ Cond { cond = c; then_block = t; else_block = e; pos = _startpos_c_ } ]
    )
# 396 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_19 =
  fun _startpos_c_ b c ->
    (
# 65 "compilateur/parser.mly"
    (
    [ Loop { cond = c; block = b; pos = _startpos_c_ } ]
    )
# 406 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_20 =
  fun b i ->
    (
# 36 "compilateur/parser.mly"
                              ( i @ b )
# 414 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_action_21 =
  fun i ->
    (
# 37 "compilateur/parser.mly"
                          ( i )
# 422 "compilateur/parser.ml"
     : (Ast.Syntax.block))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | LNequal ->
        "LNequal"
    | Ladd ->
        "Ladd"
    | LcloseP ->
        "LcloseP"
    | Ldiv ->
        "Ldiv"
    | Ldo ->
        "Ldo"
    | Lelse ->
        "Lelse"
    | Lend ->
        "Lend"
    | Leq ->
        "Leq"
    | Lequal ->
        "Lequal"
    | Lfalse _ ->
        "Lfalse"
    | Lident _ ->
        "Lident"
    | Lif ->
        "Lif"
    | Lint _ ->
        "Lint"
    | Lmul ->
        "Lmul"
    | LopenP ->
        "LopenP"
    | Lreturn ->
        "Lreturn"
    | Lsc ->
        "Lsc"
    | Lsub ->
        "Lsub"
    | Lthen ->
        "Lthen"
    | Ltrue _ ->
        "Ltrue"
    | Lvar ->
        "Lvar"
    | Lwhile ->
        "Lwhile"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_42_spec_00 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      MenhirBox_prog _v
  
  let rec _menhir_goto_prog : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState44 ->
          _menhir_run_46 _menhir_stack _v
      | MenhirState00 ->
          _menhir_run_42_spec_00 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_46 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_instr -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let MenhirCell1_instr (_menhir_stack, _menhir_s, i) = _menhir_stack in
      let b = _v in
      let _v = _menhir_action_20 b i in
      _menhir_goto_prog _menhir_stack _v _menhir_s
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_Lwhile (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState01 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState01
      | Lint _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState01 _tok
      | Lident _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState01 _tok
      | Lfalse _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState01 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_21 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_Lwhile as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldo ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Lwhile ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
          | Lvar ->
              _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
          | Lreturn ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
          | Lif ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
          | Lident _v ->
              _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState22
          | _ ->
              _eRR ())
      | Ldiv ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_Lsub (_menhir_stack, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState08 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState08 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState08 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState08 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_09 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Lsub as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP | Ldo | Lsc | Lthen ->
          let MenhirCell0_Lsub (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, left, _startpos_left_) = _menhir_stack in
          let right = _v in
          let _v = _menhir_action_09 _startpos__2_ left right in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_left_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_Lmul (_menhir_stack, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState10 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState10 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState10 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState10 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_11 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Lmul as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP | Ldo | Lsc | Lthen ->
          let MenhirCell0_Lmul (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, left, _startpos_left_) = _menhir_stack in
          let right = _v in
          let _v = _menhir_action_07 _startpos__2_ left right in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_left_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_Lequal (_menhir_stack, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState12 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState12 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState12 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState12 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_13 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Lequal as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP | Ldo | Lsc | Lthen ->
          let MenhirCell0_Lequal (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, left, _startpos_left_) = _menhir_stack in
          let right = _v in
          let _v = _menhir_action_11 _startpos__2_ left right in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_left_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_Ldiv (_menhir_stack, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState14 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState14 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState14 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState14 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Ldiv as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP | Ldo | Lsc | Lthen ->
          let MenhirCell0_Ldiv (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, left, _startpos_left_) = _menhir_stack in
          let right = _v in
          let _v = _menhir_action_10 _startpos__2_ left right in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_left_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_16 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_Ladd (_menhir_stack, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState16 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState16
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState16 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState16 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState16 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_17 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_Ladd as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP | Ldo | Lsc | Lthen ->
          let MenhirCell0_Ladd (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, left, _startpos_left_) = _menhir_stack in
          let right = _v in
          let _v = _menhir_action_08 _startpos__2_ left right in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_left_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_LNequal (_menhir_stack, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState18 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState18
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState18 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState18 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState18 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_LNequal as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP | Ldo | Lsc | Lthen ->
          let MenhirCell0_LNequal (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, left, _startpos_left_) = _menhir_stack in
          let right = _v in
          let _v = _menhir_action_12 _startpos__2_ left right in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_left_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState33 ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState29 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState27 ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState25 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState01 ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState18 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState16 ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_34 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_Lident _menhir_cell0_Leq as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lsc ->
          let MenhirCell0_Leq (_menhir_stack, _startpos__2_) = _menhir_stack in
          let MenhirCell1_Lident (_menhir_stack, _menhir_s, id, _) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_16 _startpos__2_ e id in
          _menhir_goto_instr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_instr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState44 ->
          _menhir_run_43 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_43 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState22 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState39 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState31 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_43 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsc ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Lwhile ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState44
          | Lvar ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState44
          | Lreturn ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState44
          | Lif ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState44
          | Lident _v_0 ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState44
          | Lend ->
              let i = _v in
              let _v = _menhir_action_21 i in
              _menhir_goto_prog _menhir_stack _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Lident _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Leq ->
              let _menhir_stack = MenhirCell1_Lvar (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_Lident (_menhir_stack, _v, _startpos) in
              let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
              let _menhir_stack = MenhirCell0_Leq (_menhir_stack, _startpos_0) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | Ltrue _v_1 ->
                  let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (_startpos_b_, b) = (_startpos_2, _v_1) in
                  let _v = _menhir_action_04 _startpos_b_ b in
                  _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState25 _tok
              | LopenP ->
                  _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
              | Lint _v_4 ->
                  let _startpos_5 = _menhir_lexbuf.Lexing.lex_start_p in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (_startpos_n_, n) = (_startpos_5, _v_4) in
                  let _v = _menhir_action_03 _startpos_n_ n in
                  _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState25 _tok
              | Lident _v_7 ->
                  let _startpos_8 = _menhir_lexbuf.Lexing.lex_start_p in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (_startpos_v_, v) = (_startpos_8, _v_7) in
                  let _v = _menhir_action_06 _startpos_v_ v in
                  _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState25 _tok
              | Lfalse _v_10 ->
                  let _startpos_11 = _menhir_lexbuf.Lexing.lex_start_p in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (_startpos_b_, b) = (_startpos_11, _v_10) in
                  let _v = _menhir_action_05 _startpos_b_ b in
                  _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState25 _tok
              | _ ->
                  _eRR ())
          | Lsc ->
              let (_startpos_id_, id) = (_startpos, _v) in
              let _v = _menhir_action_14 _startpos_id_ id in
              _menhir_goto_instr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_Lvar _menhir_cell0_Lident _menhir_cell0_Leq as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lsc ->
          let MenhirCell0_Leq (_menhir_stack, _startpos__3_) = _menhir_stack in
          let MenhirCell0_Lident (_menhir_stack, id, _startpos_id_) = _menhir_stack in
          let MenhirCell1_Lvar (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_15 _startpos__3_ _startpos_id_ e id in
          _menhir_goto_instr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LopenP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState03 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState03 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState03 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState03 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_07 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LopenP as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LcloseP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LopenP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_13 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _startpos__1_ _v _menhir_s _tok
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_27 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_Lreturn (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_0, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState27 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState27
      | Lint _v ->
          let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos_1, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState27 _tok
      | Lident _v ->
          let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos_2, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState27 _tok
      | Lfalse _v ->
          let _startpos_3 = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos_3, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState27 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_28 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_Lreturn as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsub ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lsc ->
          let MenhirCell1_Lreturn (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_17 _startpos__1_ e in
          _menhir_goto_instr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_29 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_Lif (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Ltrue _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos, _v) in
          let _v = _menhir_action_04 _startpos_b_ b in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState29 _tok
      | LopenP ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState29
      | Lint _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_n_, n) = (_startpos, _v) in
          let _v = _menhir_action_03 _startpos_n_ n in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState29 _tok
      | Lident _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_v_, v) = (_startpos, _v) in
          let _v = _menhir_action_06 _startpos_v_ v in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState29 _tok
      | Lfalse _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_startpos_b_, b) = (_startpos, _v) in
          let _v = _menhir_action_05 _startpos_b_ b in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState29 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_30 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_Lif as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos) in
      match (_tok : MenhirBasics.token) with
      | Lthen ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Lwhile ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState31
          | Lvar ->
              _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState31
          | Lreturn ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState31
          | Lif ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState31
          | Lident _v ->
              _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState31
          | _ ->
              _eRR ())
      | Lsub ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lmul ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Lequal ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ldiv ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer
      | Ladd ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LNequal ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_32 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_Lident (_menhir_stack, _menhir_s, _v, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Leq ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_Leq (_menhir_stack, _startpos_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Ltrue _v_1 ->
              let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_startpos_b_, b) = (_startpos_2, _v_1) in
              let _v = _menhir_action_04 _startpos_b_ b in
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState33 _tok
          | LopenP ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState33
          | Lint _v_4 ->
              let _startpos_5 = _menhir_lexbuf.Lexing.lex_start_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_startpos_n_, n) = (_startpos_5, _v_4) in
              let _v = _menhir_action_03 _startpos_n_ n in
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_n_ _v MenhirState33 _tok
          | Lident _v_7 ->
              let _startpos_8 = _menhir_lexbuf.Lexing.lex_start_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_startpos_v_, v) = (_startpos_8, _v_7) in
              let _v = _menhir_action_06 _startpos_v_ v in
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_v_ _v MenhirState33 _tok
          | Lfalse _v_10 ->
              let _startpos_11 = _menhir_lexbuf.Lexing.lex_start_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_startpos_b_, b) = (_startpos_11, _v_10) in
              let _v = _menhir_action_05 _startpos_b_ b in
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_b_ _v MenhirState33 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_35 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | Lsc ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Lwhile ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
          | Lvar ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
          | Lreturn ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
          | Lif ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
          | Lident _v_0 ->
              let _menhir_stack = MenhirCell1_instr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState36
          | Lelse | Lsc ->
              let i = _v in
              let _v = _menhir_action_02 i in
              _menhir_goto_block _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_block : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState22 ->
          _menhir_run_41 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState39 ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState31 ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_41 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_Lwhile, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, c, _startpos_c_) = _menhir_stack in
      let MenhirCell1_Lwhile (_menhir_stack, _menhir_s) = _menhir_stack in
      let b = _v in
      let _v = _menhir_action_19 _startpos_c_ b c in
      _menhir_goto_instr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_40 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_Lif, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_block -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_block (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, c, _startpos_c_) = _menhir_stack in
      let MenhirCell1_Lif (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_18 _startpos_c_ c e t in
      _menhir_goto_instr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_38 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_Lif, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_block (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | Lelse ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | Lwhile ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
          | Lvar ->
              _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
          | Lreturn ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
          | Lif ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
          | Lident _v ->
              _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState39
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_37 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_instr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_instr (_menhir_stack, _menhir_s, i) = _menhir_stack in
      let b = _v in
      let _v = _menhir_action_01 b i in
      _menhir_goto_block _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | Lwhile ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | Lvar ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | Lreturn ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | Lif ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | Lident _v ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
