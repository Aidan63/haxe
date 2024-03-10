open Common
open Globals
open Type
open Typecore
open Texpr
open Error

let rec search_for_close_field cls =
    try
        Some (PMap.find "close" cls.cl_fields)
    with Not_found ->
        begin match cls.cl_super with
        | Some (cls, _) ->
            search_for_close_field cls
        | None ->
            None
        end

let run ctx e =
    let is_autoclose_var i e = match e.eexpr with
        | TVar (var, _) when has_var_flag var VAutoClose ->
            true
        | _ ->
            false
        in
    let rec run e = match e.eexpr with
        | TBlock el ->
            begin try
                let idx, e = ExtList.List.findi is_autoclose_var el in
                let kept   = List.filteri (fun i _ -> i <= idx) el in
                let after  = run (mk (TBlock (List.filteri (fun i _ -> i > idx) el |> List.map run)) ctx.t.tvoid null_pos) in
                let close  = match e.eexpr with
                    | TVar (var, _) ->
                        let func        = TFun ([], ctx.t.tvoid) in
                        let field_type  = match follow_lazy_and_mono var.v_type with
                            | TInst (cls, params) ->
                                begin match search_for_close_field cls with
                                | Some field ->
                                    FInstance (cls, params, field)
                                | None ->
                                    raise_typing_error "Class has no close function" e.epos
                                end
                            | _ ->
                                raise_typing_error (Printf.sprintf "Unexpected type %s" (s_type_kind var.v_type)) var.v_pos
                            in
                        let mk_local    = mk (TLocal var) e.etype e.epos in
                        let mk_not_null = mk (TBinop (OpNotEq, mk_local, null var.v_type var.v_pos)) ctx.t.tbool e.epos in
                        let mk_field    = mk (TField (mk_local, field_type)) func e.epos in
                        let mk_call     = mk (TCall (mk_field, [])) ctx.t.tvoid e.epos in
                        
                        mk (TIf (mk_not_null, mk_call, None)) ctx.t.tvoid e.epos
                    | _ ->
                        raise_typing_error "Expected type" e.epos
                    in
                let exn     = alloc_var VGenerated "_hx_exn" ctx.t.tany null_pos in
                let throw   = TThrow (mk (TLocal exn) ctx.t.tany null_pos) in
                let cleanup = mk (TBlock [ close; mk throw ctx.t.tany null_pos ]) ctx.t.tvoid null_pos in
                let etry    = mk (TTry (after, [ (exn, cleanup) ])) ctx.t.tvoid null_pos in

                mk (TBlock (kept @ [ etry ] @ [ close ]) ) ctx.t.tvoid null_pos
            with Not_found ->
                e
            end
        | _ ->
            Type.map_expr run e
        in

    run e