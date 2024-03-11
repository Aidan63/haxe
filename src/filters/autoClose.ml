open Common
open Globals
open Type
open Typecore
open Texpr
open Error

let run ctx e =

    let rec find_new_autoclose_var lut idx el =
        match el with
        | [] ->
            raise Not_found
        | h::t ->
            match h.eexpr with
            | TVar(var, _) when has_var_flag var VAutoClose && Hashtbl.mem lut var.v_id = false ->
                (idx, var)
            | _ ->
                find_new_autoclose_var lut (idx + 1) t
    in

    let is_inst_close t =
        match follow t with
        | TFun ([], ret) when ExtType.is_void (follow ret) ->
            true
        | _ ->
            false
    in

    let is_abstract_close a_this t =
        match follow t with
        | TFun ([ (_, false, arg) ], ret) when ExtType.is_void (follow ret) && fast_eq arg a_this ->
            true
        | _ ->
            false
    in

    let rec search_for_close_field cls fetch validator =
        let field = try
                PMap.find "close" (fetch cls)
            with Not_found ->
                match cls.cl_super with
                | Some (cls, _) ->
                    search_for_close_field cls fetch validator
                | None ->
                    raise Not_found
            in
        match field.cf_kind with
        | Method m when m <> MethMacro && has_class_field_flag field CfPublic && validator field.cf_type ->
            field
        | _ ->
            raise Not_found
    in

    let find_close_field ctx var =
        match follow_lazy_and_mono var.v_type with
        | TInst (cls, params) ->
            begin
                try
                    let field = FInstance (cls, params, (search_for_close_field cls (fun c -> c.cl_fields) is_inst_close)) in
                    let expr  = mk (TLocal var) var.v_type null_pos in

                    (expr, field, [])
                with Not_found ->
                    raise_typing_error (Printf.sprintf "autoclose cannot be used on a variable of type %s as it has no valid close function" (s_class_path cls)) var.v_pos
            end
        | TAbstract (abs, params) ->
            begin match abs.a_impl with
            | Some cls ->
                begin try
                    let field = FStatic (cls, (search_for_close_field cls (fun c -> c.cl_statics) (is_abstract_close abs.a_this))) in
                    let expr  = mk (TIdent (s_type_path cls.cl_path)) (TInst (cls, params)) null_pos in

                    (expr, field, [ mk (TLocal var) var.v_type null_pos ])
                with Not_found ->
                    raise_typing_error (Printf.sprintf "autoclose cannot be used on a variable of type %s as it has no valid close function" (s_type_path abs.a_path)) var.v_pos
                end
            | None ->
                raise_typing_error "autoclose cannot be used on an abstract with no implementation" var.v_pos
            end
        | other ->
            raise_typing_error (Printf.sprintf "Unexpected type %s" (s_type_kind other)) var.v_pos
    in

    let rec run lut e = match e.eexpr with
        | TBlock el ->
            begin try
                let idx, var = find_new_autoclose_var lut 0 el in
                let close =
                    Hashtbl.add lut var.v_id ();

                    let f_expr, f_type, f_args = find_close_field ctx var in
                    let mk_local    = mk (TLocal var) var.v_type null_pos in
                    let mk_field    = mk (TField (f_expr, f_type)) var.v_type null_pos in
                    let mk_call     = mk (TCall (mk_field, f_args)) ctx.t.tvoid null_pos in
                    let mk_not_null = mk (TBinop (OpNotEq, mk_local, null var.v_type var.v_pos)) ctx.t.tbool null_pos in
                
                    mk (TIf (mk_not_null, mk_call, None)) ctx.t.tvoid null_pos
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