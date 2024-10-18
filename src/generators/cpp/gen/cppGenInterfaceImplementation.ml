open Ast
open Type
open Error
open Common
open Globals
open CppStrings
open CppExprUtils
open CppTypeUtils
open CppAst
open CppAstTools
open CppSourceWriter
open CppContext
open CppGen

let gen_field_init ctx class_def field =
  let dot_name = join_class_path class_def.cl_path "." in
  let remap_name = keyword_remap field.cf_name in

  match field.cf_expr with
  | Some expr ->
    let var_name =
      match remap_name with
      | "__meta__" -> "__mClass->__meta__"
      | "__rtti" -> "__mClass->__rtti__"
      | _ -> remap_name
    in

    gen_cpp_init ctx dot_name "boot" (var_name ^ " = ") expr
  | _ -> ()

let cpp_get_interface_slot ctx name =
  try Hashtbl.find !(ctx.ctx_interface_slot) name
  with Not_found ->
    let result = !(ctx.ctx_interface_slot_count) in
    Hashtbl.replace !(ctx.ctx_interface_slot) name result;
    ctx.ctx_interface_slot_count := !(ctx.ctx_interface_slot_count) + 1;
    result

let generate_protocol_delegate ctx class_def output =
  let protocol = get_meta_string class_def.cl_meta Meta.ObjcProtocol |> Option.default "" in
  let full_class_name = ("::" ^ join_class_path_remap class_def.cl_path "::") ^ "_obj" in
  let name = "_hx_" ^ protocol ^ "_delegate" in
  output ("@interface " ^ name ^ " : NSObject<" ^ protocol ^ "> {\n");
  output "\t::hx::Object *haxeObj;\n";
  output "}\n";
  output "@end\n\n";
  output ("@implementation " ^ name ^ "\n");
  output "- (id)initWithImplementation:( ::hx::Object *)inInplemnetation {\n";
  output "  if (self = [super init]) {\n";
  output "     self->haxeObj = inInplemnetation;\n";
  output "     GCAddRoot(&self->haxeObj);\n";
  output "  }\n";
  output "  return self;\n";
  output "}\n";
  output "- (void)dealloc {\n";
  output "   GCRemoveRoot(&self->haxeObj);\n";
  output "   #ifndef OBJC_ARC\n";
  output "   [super dealloc];\n";
  output "   #endif\n";
  output "}\n\n";

  let dump_delegate field =
    match field.cf_type with
    | TFun (args, ret) ->
      let retStr = type_to_string ret in
      let fieldName, argNames =
        match get_meta_string field.cf_meta Meta.ObjcProtocol with
        | Some nativeName ->
          let parts = ExtString.String.nsplit nativeName ":" in
          (List.hd parts, parts)
        | None -> (field.cf_name, List.map (fun (n, _, _) -> n) args)
      in
      output ("- (" ^ retStr ^ ") " ^ fieldName);

      let first = ref true in
      (try
          List.iter2
            (fun (name, _, argType) signature_name ->
              if !first then
                output (" :(" ^ type_to_string argType ^ ")" ^ name)
              else
                output
                  (" " ^ signature_name ^ ":(" ^ type_to_string argType ^ ")"
                ^ name);
              first := false)
            args argNames
        with Invalid_argument _ ->
          abort
            (let argString =
              String.concat "," (List.map (fun (name, _, _) -> name) args)
            in
            "Invalid arg count in delegate in " ^ field.cf_name ^ " '"
            ^ field.cf_name ^ "," ^ argString ^ "' != '"
            ^ String.concat "," argNames ^ "'")
            field.cf_pos);
      output " {\n";
      output "\t::hx::NativeAttach _hx_attach;\n";
      output
        ((if retStr = "void" then "\t" else "\treturn ")
        ^ full_class_name ^ "::"
        ^ keyword_remap field.cf_name
        ^ "(haxeObj");
      List.iter (fun (name, _, _) -> output ("," ^ name)) args;
      output ");\n}\n\n"
    | _ -> ()
  in
  List.iter dump_delegate class_def.cl_ordered_fields;

  output "@end\n\n"

let generate_managed_interface baseCtx class_def =
  let common_ctx = baseCtx.ctx_common in
  let class_path = class_def.cl_path in
  let debug = baseCtx.ctx_debug_level in
  let cpp_file = new_placed_cpp_file baseCtx.ctx_common class_path in
  let cpp_ctx = file_context baseCtx cpp_file debug false in
  let ctx = cpp_ctx in
  let output_cpp = cpp_file#write in
  let strq = strq ctx.ctx_common in
  let scriptable = Common.defined common_ctx Define.Scriptable && not class_def.cl_private in

  if debug > 1 then
    print_endline
      ("Found class definition:" ^ join_class_path class_def.cl_path "::");

  cpp_file#write_h "#include <hxcpp.h>\n\n";

  let all_referenced =
    CppReferences.find_referenced_types ctx (TClassDecl class_def) ctx.ctx_super_deps
    ctx.ctx_constructor_deps false false scriptable
  in
  List.iter (add_include cpp_file) all_referenced;

  if scriptable then cpp_file#write_h "#include <hx/Scriptable.h>\n";

  cpp_file#write_h "\n";

  output_cpp (get_class_code class_def Meta.CppFileCode);
  let includes = get_all_meta_string_path class_def.cl_meta Meta.CppInclude in
  let printer inc = output_cpp ("#include \"" ^ inc ^ "\"\n") in
  List.iter printer includes;

  begin_namespace output_cpp class_path;
  output_cpp "\n";

  output_cpp (get_class_code class_def Meta.CppNamespaceCode);

  let class_name = class_name class_def in

  output_cpp "\n";

  (* cl_interface *)
  let implemented_instance_fields = List.filter should_implement_field class_def.cl_ordered_fields in
  let reflective_members = List.filter (reflective class_def) implemented_instance_fields in
  let sMemberFields =
    match reflective_members with
    | [] -> "0 /* sMemberFields */"
    | _ ->
      let memberFields = class_name ^ "_sMemberFields" in
      let dump_field_name field = output_cpp ("\t" ^ strq field.cf_name ^ ",\n") in
      output_cpp ("static ::String " ^ memberFields ^ "[] = {\n");
      List.iter dump_field_name reflective_members;
      output_cpp "\t::String(null()) };\n\n";
      memberFields
  in

  if scriptable then (
    let dump_script_field idx (field, f_args, return_t) =
      let args = print_tfun_arg_list true f_args in
      let return_type = type_to_string return_t in
      let ret = if return_type = "Void" || return_type = "void" then " " else "return " in
      let name = keyword_remap field.cf_name in

      output_cpp ("\t" ^ return_type ^ " " ^ name ^ "( " ^ args ^ " ) {\n");
      output_cpp "\t\t::hx::CppiaCtx *__ctx = ::hx::CppiaCtx::getCurrent();\n";
      output_cpp "\t\t::hx::AutoStack __as(__ctx);\n";
      output_cpp "\t\t__ctx->pushObject(this);\n";
      List.iter
        (fun (name, opt, t) ->
          output_cpp
            ("\t\t__ctx->push" ^ CppCppia.script_type t opt ^ "("
            ^ keyword_remap name ^ ");\n"))
        f_args;
      let interfaceSlot = string_of_int (-cpp_get_interface_slot ctx name) in
      output_cpp
        ("\t\t" ^ ret ^ "__ctx->run"
        ^ CppCppia.script_type return_t false
        ^ "(__GetScriptVTable()[" ^ interfaceSlot ^ "]);\n");
      output_cpp "\t}\n";
    in

    let sctipt_name = class_name ^ "__scriptable" in

    output_cpp ("class " ^ sctipt_name ^ " : public ::hx::Object {\n");
    output_cpp "public:\n";

    let list_iteri func in_list =
      let idx = ref 0 in
      List.iter
        (fun elem ->
          func !idx elem;
          idx := !idx + 1)
        in_list
    in

    list_iteri dump_script_field (all_virtual_functions class_def);
    output_cpp "};\n\n";

    let generate_script_function field scriptName callName =
      match follow field.cf_type with
      | TFun (args, return_type) when not (is_data_member field) ->
        output_cpp ("\nstatic void CPPIA_CALL " ^ scriptName ^ "(::hx::CppiaCtx *ctx) {\n");
        let ret =
          match cpp_type_of return_type with
          | TCppScalar "bool" -> "b"
          | _ -> CppCppia.script_signature return_type false in
        if ret <> "v" then
          output_cpp ("ctx->return" ^ CppCppia.script_type return_type false ^ "(");

        let signature =
          output_cpp (class_name ^ "::" ^ callName ^ "(ctx->getThis()" ^ if List.length args > 0 then "," else "");

          let signature, _, _ =
            List.fold_left
              (fun (signature, sep, size) (_, opt, t) ->
                output_cpp
                  (sep ^ "ctx->get" ^ CppCppia.script_type t opt ^ "(" ^ size
                  ^ ")");
                ( signature ^ CppCppia.script_signature t opt,
                  ",",
                  size ^ "+sizeof(" ^ CppCppia.script_size_type t opt ^ ")" ))
              (ret, "", "sizeof(void*)") args in
          output_cpp ")";
          signature
        in

        if ret <> "v" then output_cpp ")";
        output_cpp ";\n}\n";
        signature
      | _ -> ""
    in

    let sigs = Hashtbl.create 0 in
    let new_sctipt_functions = all_virtual_functions class_def in
    match new_sctipt_functions with
    | [] ->
      output_cpp "static ::hx::ScriptNamedFunction *__scriptableFunctions = 0;\n"
    | _ ->
      List.iter
        (fun (f, _, _) ->
          let s = generate_script_function f ("__s_" ^ f.cf_name) (keyword_remap f.cf_name) in
          Hashtbl.add sigs f.cf_name s)
        new_sctipt_functions;

      output_cpp "#ifndef HXCPP_CPPIA_SUPER_ARG\n";
      output_cpp "#define HXCPP_CPPIA_SUPER_ARG(x)\n";
      output_cpp "#endif\n";
      output_cpp "static ::hx::ScriptNamedFunction __scriptableFunctions[] = {\n";
      let dump_func f isStaticFlag =
        let s = try Hashtbl.find sigs f.cf_name with Not_found -> "v" in
        output_cpp
          ("  ::hx::ScriptNamedFunction(\"" ^ f.cf_name ^ "\",__s_" ^ f.cf_name
         ^ ",\"" ^ s ^ "\", " ^ isStaticFlag ^ " ");
        let superCall =
          if isStaticFlag = "true" || has_class_flag class_def CInterface then
            "0"
          else "__s_" ^ f.cf_name ^ "<true>"
        in
        output_cpp ("HXCPP_CPPIA_SUPER_ARG(" ^ superCall ^ ")");
        output_cpp " ),\n"
      in
      List.iter (fun (f, _, _) -> dump_func f "false") new_sctipt_functions;
      output_cpp "  ::hx::ScriptNamedFunction(0,0,0 HXCPP_CPPIA_SUPER_ARG(0) ) };\n";

    output_cpp ("\n\n" ^ class_name ^ " " ^ class_name ^ "_scriptable = {\n");
    List.iter
      (fun (f, args, return_type) ->
        let cast = cpp_tfun_signature true args return_type in
        output_cpp
          ("\t" ^ cast ^ "&" ^ sctipt_name ^ "::" ^ keyword_remap f.cf_name ^ ",\n"))
      new_sctipt_functions;
    output_cpp "};\n");

  let class_name_text = join_class_path class_path "." in

  output_cpp ("::hx::Class " ^ class_name ^ "::__mClass;\n\n");

  output_cpp ("void " ^ class_name ^ "::__register()\n{\n");

  output_cpp "\t::hx::Static(__mClass) = new ::hx::Class_obj();\n";
  output_cpp ("\t__mClass->mName = " ^ strq class_name_text ^ ";\n");
  output_cpp "\t__mClass->mSuper = &super::__SGetClass();\n";
  output_cpp ("\t__mClass->mMembers = ::hx::Class_obj::dupFunctions(" ^ sMemberFields ^ ");\n");
  output_cpp ("\t__mClass->mCanCast = ::hx::TIsInterface< (int)" ^ cpp_class_hash class_def ^ " >;\n");
  output_cpp "\t::hx::_hx_RegisterClass(__mClass->mName, __mClass);\n";
  if scriptable then
    output_cpp ("  HX_SCRIPTABLE_REGISTER_INTERFACE(\"" ^ class_name_text ^ "\"," ^ class_name ^ ");\n");
  output_cpp "}\n\n";

  if has_boot_field class_def then (
    output_cpp ("void " ^ class_name ^ "::__boot()\n{\n");

    List.iter
      (gen_field_init ctx class_def)
      (List.filter should_implement_field class_def.cl_ordered_statics);

    output_cpp "}\n\n");

  end_namespace output_cpp class_path;

  if Meta.has Meta.ObjcProtocol class_def.cl_meta then (
    let full_class_name = ("::" ^ join_class_path_remap class_path "::") ^ "_obj" in
    let protocol = get_meta_string class_def.cl_meta Meta.ObjcProtocol |> Option.default "" in
    generate_protocol_delegate ctx class_def output_cpp;
    output_cpp ("id<" ^ protocol ^ "> " ^ full_class_name ^ "::_hx_toProtocol(Dynamic inImplementation) {\n");
    output_cpp ("\treturn [ [_hx_" ^ protocol ^ "_delegate alloc] initWithImplementation:inImplementation.mPtr];\n");
    output_cpp "}\n\n");

  cpp_file#close