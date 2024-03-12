open Common
open Globals
open Type
open Typecore
open Texpr
open Error
open Ast

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

    let find_close_field ctx var =
        let rec loop t = 
            match follow t with
            | TInst (cls, params) ->
                begin
                    try
                        let found = match TClass.get_all_fields cls params |> PMap.find "close" with
                        | (_, field) when has_class_field_flag field CfPublic && is_inst_close field.cf_type -> field
                        | _ -> raise Not_found in
                        let field = FInstance (cls, params, found) in
                        let expr  = mk (TLocal var) var.v_type null_pos in

                        (expr, field, [])
                    with Not_found ->
                        raise_typing_error (Printf.sprintf "autoclose cannot be used on a variable of type %s as it has no valid close function" (s_class_path cls)) var.v_pos
                end
            | TAbstract ({ a_impl = Some cls; a_enum = false } as a, params) ->
                begin try
                    match find_field cls "close" CfrStatic with
                    | found when has_class_field_flag found CfPublic && has_class_field_flag found CfImpl && is_abstract_close a.a_this found.cf_type ->
                        let field = FStatic (cls, found) in
                        let expr  = mk (TIdent (s_type_path cls.cl_path)) (TInst (cls, params)) null_pos in

                        (expr, field, [ mk (TLocal var) var.v_type null_pos ])
                    | _ ->
                        raise Not_found
                with Not_found ->
                    try
                        let _,el,_ = Meta.get Meta.Forward a.a_meta in
                        match ExtList.List.exists (fun e -> match fst e with EConst(Ident "close") -> true | _ -> false) el with
                        | true -> loop a.a_this
                        | false -> raise Not_found
                    with Not_found ->
                        raise_typing_error (Printf.sprintf "autoclose cannot be used on a variable of type %s as it has no valid close function" (s_class_path cls)) var.v_pos
                end
            | other ->
                raise_typing_error (Printf.sprintf "autoclose cannot be used on a variable of type %s" (s_type_kind other)) var.v_pos
        in
        loop var.v_type
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
                { e with eexpr = TBlock( el |> List.map (run lut) ) }
            end
        | _ ->
            Type.map_expr (run lut) e
    in

    run (Hashtbl.create 0) e