open Common
open Globals
open Type
open Typecore
open Texpr
open Error
open Ast

type ac_ctx = {
    blocks : texpr Stack.t;
    loops : texpr Stack.t Stack.t;
    lut : (int, unit) Hashtbl.t;
    typer : typer;
}

let run tctx e =

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

    and is_inst_close t =
        match follow t with
        | TFun ([], ret) when ExtType.is_void (follow ret) ->
            true
        | _ ->
            false
    
    and is_abstract_close a_this t =
        match follow t with
        | TFun ([ (_, false, arg) ], ret) when ExtType.is_void (follow ret) && fast_eq arg a_this ->
            true
        | _ ->
            false
    
    and find_close_field var =
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

    and block_scope ctx p e els =
        begin try
            let idx, var = find_new_autoclose_var ctx.lut 0 els in
            let kept     = ExtList.List.filteri (fun i _ -> i < idx) els |> List.map (map ctx) in
            let close    =
                let f_expr, f_type, f_args = find_close_field var in
                let mk_local    = mk (TLocal var) var.v_type null_pos in
                let mk_field    = mk (TField (f_expr, f_type)) var.v_type null_pos in
                let mk_call     = mk (TCall (mk_field, f_args)) ctx.typer.t.tvoid null_pos in
                let mk_not_null = mk (TBinop (OpNotEq, mk_local, null var.v_type var.v_pos)) ctx.typer.t.tbool null_pos in
            
                mk (TIf (mk_not_null, mk_call, None)) ctx.typer.t.tvoid null_pos
            in

            Hashtbl.add ctx.lut var.v_id ();
            Stack.push close ctx.blocks;

            if Stack.is_empty ctx.loops = false then
                Stack.push close (Stack.top ctx.loops);

            let after   = ExtList.List.filteri (fun i _ -> i > idx) els in
            let trying  = after |> block_scope ctx p (mk (TBlock after) ctx.typer.t.tvoid null_pos) in
            let exn     = alloc_var VGenerated "_hx_exn" ctx.typer.t.tany null_pos in
            let throw   = TThrow (mk (TLocal exn) ctx.typer.t.tany null_pos) in
            let cleanup = mk (TBlock [ close; mk throw ctx.typer.t.tany null_pos ]) ctx.typer.t.tvoid null_pos in
            let etry    = mk (TTry (trying, [ (exn, cleanup) ])) ctx.typer.t.tvoid null_pos in

            Stack.pop ctx.blocks |> ignore;

            mk (TBlock (kept @ [ List.nth els idx ] @ [ etry ] @ [ close ]) ) ctx.typer.t.tvoid null_pos
        with Not_found ->
            { e with eexpr = TBlock(els |> List.map (map ctx)) }
        end

    and map ctx e = match e.eexpr with
        | TBlock els ->
            block_scope ctx e.epos e els
        | TReturn None when Stack.is_empty ctx.blocks = false ->
            let func acc cur = acc @ [ cur ] in
            let exprs = Stack.fold func [] ctx.blocks in

            mk (TBlock (exprs @ [ e ])) e.etype null_pos
        | TReturn Some inner when Stack.is_empty ctx.blocks = false ->
            let tmp          = alloc_var VGenerated "_hx_tmp" inner.etype null_pos in
            let assignment   = mk (TVar (tmp, Some inner)) inner.etype null_pos in
            let func acc cur = acc @ [ cur ] in
            let exprs        = Stack.fold func [] ctx.blocks in
            let return       = mk (TReturn (Some (mk (TLocal tmp) tmp.v_type null_pos))) e.etype null_pos in

            mk (TBlock ( [ assignment ] @ exprs @ [ return ])) e.etype null_pos
        | TFor (v,e1,e2) ->
            Stack.push (Stack.create()) ctx.loops;
            let mapped = { e with eexpr = TFor (v,map ctx e1,map ctx e2) } in
            Stack.pop ctx.loops |> ignore;

            mapped
        | TWhile (e1,e2,flag) ->
            Stack.push (Stack.create()) ctx.loops;
            let mapped = { e with eexpr = TWhile (map ctx e1,map ctx e2,flag) } in
            Stack.pop ctx.loops |> ignore;

            mapped
        | TContinue when Stack.is_empty ctx.loops = false -> 
            let func acc cur = acc @ [ cur ] in
            let exprs  = Stack.fold func [] (Stack.top ctx.loops) in

            mk (TBlock (exprs @ [ e ])) e.etype null_pos
        | TBreak when Stack.is_empty ctx.loops = false ->
            let func acc cur = acc @ [ cur ] in
            let exprs  = Stack.fold func [] (Stack.top ctx.loops) in

            mk (TBlock (exprs @ [ e ])) e.etype null_pos
        | TFunction fu ->
            { e with eexpr = TFunction { fu with tf_expr = map { typer = tctx; blocks = Stack.create(); loops = Stack.create(); lut = Hashtbl.create 0; } fu.tf_expr } }
        | _ ->
            Type.map_expr (map ctx) e
    in

    map { typer = tctx; blocks = Stack.create(); loops = Stack.create(); lut = Hashtbl.create 0; } e