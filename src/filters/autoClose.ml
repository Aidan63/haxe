open Common
open Globals
open Type
open Typecore
open Texpr
open Error

let run ctx e =

    let is_new_autoclose_var lut i e =
        match e.eexpr with
        | TVar (var, _) when has_var_flag var VAutoClose ->
            begin match Hashtbl.find_opt lut var.v_id with
            | Some _ -> false
            | None -> true
            end
        | _ ->
            false
        in

    let rec search_for_close_field cls =
        try
            PMap.find "close" cls.cl_fields
        with Not_found ->
            match cls.cl_super with
            | Some (cls, _) ->
                search_for_close_field cls
            | None ->
                raise Not_found
        in

    let find_close_field var =
        match follow_lazy_and_mono var.v_type with
        | TInst (cls, params) ->
            begin
                try
                    FInstance (cls, params, (search_for_close_field cls))
                with Not_found ->
                    raise_typing_error (Printf.sprintf "%s has no close function" (s_class_path cls)) var.v_pos
            end
        | _ -> raise_typing_error (Printf.sprintf "Unexpected type %s" (s_type_kind var.v_type)) var.v_pos
        in

    let rec run lut e = match e.eexpr with
        | TBlock el ->
            begin try
                let idx, e = ExtList.List.findi (is_new_autoclose_var lut) el in
                let close  = match e.eexpr with
                    | TVar (var, _) ->
                        Hashtbl.add lut var.v_id ();

                        let func        = TFun ([], ctx.t.tvoid) in
                        let field_type  = find_close_field var in
                        let mk_local    = mk (TLocal var) e.etype null_pos in
                        let mk_field    = mk (TField (mk_local, field_type)) func null_pos in
                        let mk_call     = mk (TCall (mk_field, [])) ctx.t.tvoid null_pos in
                        let mk_not_null = mk (TBinop (OpNotEq, mk_local, null var.v_type var.v_pos)) ctx.t.tbool null_pos in
                        
                        mk (TIf (mk_not_null, mk_call, None)) ctx.t.tvoid null_pos
                    | _ ->
                        raise_typing_error (Printf.sprintf "Unxpected type %s" (s_type_kind e.etype)) e.epos
                    in
                let kept    = List.filteri (fun i _ -> i <= idx) el in
                let after   = mk (TBlock (List.filteri (fun i _ -> i > idx) el |> List.map (run lut))) ctx.t.tvoid null_pos |> run lut in
                let exn     = alloc_var VGenerated "_hx_exn" ctx.t.tany null_pos in
                let throw   = TThrow (mk (TLocal exn) ctx.t.tany null_pos) in
                let cleanup = mk (TBlock [ close; mk throw ctx.t.tany null_pos ]) ctx.t.tvoid null_pos in
                let etry    = mk (TTry (after, [ (exn, cleanup) ])) ctx.t.tvoid null_pos in

                mk (TBlock (kept @ [ etry ] @ [ close ]) ) ctx.t.tvoid null_pos
            with Not_found ->
                e
            end
        | _ ->
            Type.map_expr (run lut) e
        in

    run (Hashtbl.create 0) e