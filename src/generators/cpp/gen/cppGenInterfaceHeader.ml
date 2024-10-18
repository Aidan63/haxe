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

let calculate_debug_level interface_def base_ctx =
  if Meta.has Meta.NoDebug interface_def.cl_meta || Common.defined base_ctx.ctx_common Define.NoDebug then
    0
  else
    1

let attribs common_ctx = match Common.defined common_ctx Define.DllExport with
  | true -> "HXCPP_EXTERN_CLASS_ATTRIBUTES"
  | false -> "HXCPP_CLASS_ATTRIBUTES"

let gen_member_def ctx class_def is_static field =
  match (follow field.cf_type, field.cf_kind) with
  | _, Method MethDynamic -> ()
  | TFun (args, return_type), Method _ ->
    let output     = ctx.ctx_output in
    let remap_name = keyword_remap field.cf_name in
    let nativeGen  = Meta.has Meta.NativeGen class_def.cl_meta in
    let gen_args   = print_tfun_arg_list true in

    if is_static || nativeGen then (
      output ((if is_static then "\t\t" else "\t\tvirtual ") ^ type_to_string return_type);
      output (" " ^ remap_name ^ "( ");
      output (gen_args args);
      output (if is_static then ");\n" else ")=0;\n");
      if reflective class_def field then
        if Common.defined ctx.ctx_common Define.DynamicInterfaceClosures then
          output
            ("\t\tinline ::Dynamic " ^ remap_name
            ^ "_dyn() { return __Field( "
            ^ strq ctx.ctx_common field.cf_name
            ^ ", ::hx::paccDynamic); }\n")
        else
          output ("\t\tvirtual ::Dynamic " ^ remap_name ^ "_dyn()=0;\n"))
    else
      let argList      = gen_args args in
      let returnType   = type_to_string return_type in
      let returnStr    = if returnType = "void" then "" else "return " in
      let commaArgList = if argList = "" then argList else "," ^ argList in
      let cast =
        "::hx::interface_cast< ::"
        ^ join_class_path_remap class_def.cl_path "::"
        ^ "_obj *>"
      in
      output ("\t\t" ^ returnType ^ " (::hx::Object :: *_hx_" ^ remap_name ^ ")(" ^ argList ^ "); \n");
      output ("\t\tstatic inline " ^ returnType ^ " " ^ remap_name ^ "( ::Dynamic _hx_" ^ commaArgList ^ ") {\n");
      output "\t\t\t#ifdef HXCPP_CHECK_POINTER\n";
      output "\t\t\tif (::hx::IsNull(_hx_)) ::hx::NullReference(\"Object\", false);\n";
      output "\t\t\t#ifdef HXCPP_GC_CHECK_POINTER\n";
      output "\t\t\t\tGCCheckPointer(_hx_.mPtr);\n";
      output "\t\t\t#endif\n";
      output "\t\t\t#endif\n";
      output
        ("\t\t\t" ^ returnStr ^ "(_hx_.mPtr->*( " ^ cast
        ^ "(_hx_.mPtr->_hx_getInterface(" ^ cpp_class_hash class_def
        ^ ")))->_hx_" ^ remap_name ^ ")(" ^ print_arg_names args
        ^ ");\n\t\t}\n")
  | _ -> ()

let gen_includes h_file interface_def =
  let add_class_includes cls =
    match get_all_meta_string_path cls.cl_meta Meta.Include with
    | [] ->
      h_file#add_include cls.cl_path
    | includes ->
      List.iter (fun inc -> h_file#add_include (path_of_string inc)) includes in

  (* Include the real header file for the super class *)
  match interface_def.cl_super with
  | Some (cls, _) -> add_class_includes cls
  | _ -> ();

  (* And any interfaces ... *)
  interface_def.cl_implements
    |> real_interfaces
    |> List.iter (fun (cls, _) -> add_class_includes cls)

let gen_forward_decls h_file interface_def ctx common_ctx =
  (* Only need to forward-declare classes that are mentioned in the header file (ie, not the implementation) *)
  let scriptable = Common.defined common_ctx Define.Scriptable && not interface_def.cl_private in
  let header_referenced, header_flags =
    CppReferences.find_referenced_types_flags ctx (TClassDecl interface_def) "*" ctx.ctx_super_deps (Hashtbl.create 0) true false scriptable
  in

  List.iter2
    (fun r f -> gen_forward_decl h_file r f)
    header_referenced header_flags

let gen_header_includes interface_def output_h =
  output_h "\n";
  output_h (get_class_code interface_def Meta.HeaderCode);
  let includes = get_all_meta_string_path interface_def.cl_meta Meta.HeaderInclude in
  let printer inc = output_h ("#include \"" ^ inc ^ "\"\n") in
  List.iter printer includes

let gen_body interface_def ctx output_h =
  if has_boot_field interface_def then output_h "\t\tstatic void __boot();\n";

  match interface_def.cl_array_access with
  | Some t -> output_h ("\t\ttypedef " ^ type_string t ^ " __array_access;\n")
  | _ -> ();

  interface_def.cl_ordered_statics
    |> List.filter should_implement_field
    |> List.iter (gen_member_def ctx interface_def true);

  interface_def
    |> all_virtual_functions
    |> List.iter (fun (field, _, _) -> gen_member_def ctx interface_def false field);

  match get_meta_string interface_def.cl_meta Meta.ObjcProtocol with
  | Some protocol ->
    output_h ("\t\tstatic id<" ^ protocol ^ "> _hx_toProtocol(Dynamic inImplementation);\n")
  | None ->
    ();

  output_h (get_class_code interface_def Meta.HeaderClassCode)

let generate_native_interface base_ctx interface_def =
  let common_ctx = base_ctx.ctx_common in
  let class_path = interface_def.cl_path in
  let class_name = class_name interface_def in

  let parent, super =
    match interface_def.cl_super with
    | Some (klass, params) ->
        let name = tcpp_to_string_suffix "_obj" (cpp_instance_type klass params) in
        ( "virtual " ^ name, name )
    | None ->
        ("virtual ::hx::NativeInterface", "::hx::NativeInterface")
  in

  let h_file     = new_header_file common_ctx common_ctx.file class_path in
  let debug      = calculate_debug_level interface_def base_ctx in
  let ctx        = file_context base_ctx h_file debug true in
  let output_h   = h_file#write in
  let def_string = join_class_path class_path "_" in

  begin_header_file h_file#write_h def_string true;

  gen_includes h_file interface_def;
  gen_forward_decls h_file interface_def ctx common_ctx;
  gen_header_includes interface_def output_h;

  begin_namespace output_h class_path;
  output_h "\n\n";
  output_h (get_class_code interface_def Meta.HeaderNamespaceCode);

  output_h ("class " ^ (attribs common_ctx) ^ " " ^ class_name ^ " : public " ^ parent);
  
  interface_def.cl_implements
    |> List.filter (fun (t, _) -> is_native_gen_class t)
    |> List.iter (fun (c, _) -> output_h (" , public virtual " ^ join_class_path c.cl_path "::"));

  output_h "\n{\n\tpublic:\n";
  output_h ("\t\ttypedef " ^ super ^ " super;\n");
  output_h ("\t\ttypedef " ^ class_name ^ " OBJ_;\n");

  CppGen.generate_native_constructor ctx output_h interface_def true;

  gen_body interface_def ctx output_h;
  
  output_h "};\n\n";

  end_namespace output_h class_path;
  end_header_file output_h def_string;

  h_file#close

let generate_managed_interface base_ctx interface_def =
  let common_ctx = base_ctx.ctx_common in
  let class_path = interface_def.cl_path in
  let class_name = class_name interface_def in

  let parent, super =
    match interface_def.cl_super with
    | Some (klass, params) ->
      let name = tcpp_to_string_suffix "_obj" (cpp_instance_type klass params) in
      ( name, name )
    | None ->
      ("", "::hx::Object")
  in
  let h_file     = new_header_file common_ctx common_ctx.file class_path in
  let debug      = calculate_debug_level interface_def base_ctx in
  let ctx        = file_context base_ctx h_file debug true in
  let output_h   = h_file#write in
  let def_string = join_class_path class_path "_" in

  begin_header_file h_file#write_h def_string false;

  gen_includes h_file interface_def;
  gen_forward_decls h_file interface_def ctx common_ctx;
  gen_header_includes interface_def output_h;

  begin_namespace output_h class_path;
  output_h "\n\n";
  output_h (get_class_code interface_def Meta.HeaderNamespaceCode);

  output_h ("class " ^ (attribs common_ctx) ^ " " ^ class_name ^ " {\n");
  output_h "\tpublic:\n";
  output_h ("\t\ttypedef " ^ super ^ " super;\n");
  output_h "\t\tHX_DO_INTERFACE_RTTI;\n\n";

  gen_body interface_def ctx output_h;
  
  output_h "};\n\n";

  end_namespace output_h class_path;
  end_header_file output_h def_string;

  h_file#close