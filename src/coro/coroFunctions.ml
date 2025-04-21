open Globals
open Type
open CoroTypes

let make_block ctx typepos =
	let id = ctx.next_block_id in
	ctx.next_block_id <- ctx.next_block_id + 1;
	{
		cb_id = id;
		cb_el = DynArray.create ();
		cb_typepos = typepos;
		cb_next = NextUnknown;
		cb_catch = ctx.current_catch;
		cb_flags = 0;
	}

let add_block_flag cb (flag : cb_flag) =
	cb.cb_flags <- set_flag cb.cb_flags (Obj.magic flag)

let has_block_flag cb (flag : cb_flag) =
	has_flag cb.cb_flags (Obj.magic flag)