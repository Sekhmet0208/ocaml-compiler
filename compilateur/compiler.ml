open Ast.IR
open Mips
module Env = Map.Make (String)

type cinfo = { asm : Mips.instr list; env : Mips.loc Env.t; fpo : int }

let new_label =
  let counter = ref 0 in
  fun () ->
    incr counter;
    "l" ^ string_of_int !counter

let rec compile_expr e env =
  match e with
  | Int n -> [ Li (V0, n) ]
  | Bool b -> [ Li (V0, if b then 1 else 0) ]
  | Var v -> [ Lw (V0, Env.find v env) ]
  | Call (f, args) ->
      let ca =
        List.map
          (fun a ->
            compile_expr a env @ [ Addi (SP, SP, -4); Sw (V0, Mem (SP, 0)) ])
          args
      in
      List.flatten ca @ [ Jal f; Addi (SP, SP, 4 * List.length args) ]

let rec compile_instr instr info =
  match instr with
  | DeclVar v ->
      {
        info with
        fpo = info.fpo - 4;
        env = Env.add v (Mem (FP, info.fpo)) info.env;
      }
  | Assign (v, e) ->
      {
        info with
        asm =
          info.asm @ compile_expr e info.env @ [ Sw (V0, Env.find v info.env) ];
      }
  | Return e ->
      let compiled_expr = compile_expr e info.env in
      { info with asm = info.asm @ compiled_expr @ [ Move (SP, FP); Jr RA ] }
  | Cond (cond, then_block, else_block) ->
      let else_label = new_label () in
      let end_label = new_label () in
      let new_info =
        {
          info with
          asm =
            info.asm @ compile_expr cond info.env @ [ Beqz (V0, else_label) ];
        }
      in
      let info_then = compile_block then_block new_info in
      let info_turbo_then =
        {
          info_then with
          asm = info_then.asm @ [ Jal end_label; Label else_label ];
        }
      in
      let info_else = compile_block else_block info_turbo_then in
      let info_turbo_else =
        { info_else with asm = info_else.asm @ [ Label end_label ] }
      in

      info_turbo_else
  | Loop (cond, block) ->
      let loop_label = new_label () in
      let end_label = new_label () in
      let new_info =
        {
          info with
          asm = info.asm @ compile_expr cond info.env @ [ Beqz (V0, end_label) ];
        }
      in
      let info_loop = compile_block block new_info in
      let info_turbo_loop =
        {
          info_loop with
          asm = info_loop.asm @ [ B loop_label; Label end_label ];
        }
      in

      { info_turbo_loop with asm = info.asm @ [ Label loop_label ] }

and compile_block block info =
  match block with
  | i :: b ->
      let new_info = compile_instr i info in
      compile_block b new_info
  | [] -> info

let compile ir =
  let info =
    compile_block ir { asm = Baselib.builtins; env = Env.empty; fpo = 0 }
  in
  { text = Move (FP, SP) :: Addi (FP, SP, info.fpo) :: info.asm; data = [] }
