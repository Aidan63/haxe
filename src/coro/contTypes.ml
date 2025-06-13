open Type

type continuation_api = {
	base_continuation_class : tclass;
	immediate_suspension_result_class : tclass;
	state : tclass_field;
	result : tclass_field;
	error : tclass_field;
	completion : tclass_field;
	context : tclass_field;
	goto_label : tclass_field;
	recursing : tclass_field;
	immediate_result : texpr -> texpr;
	immediate_error : texpr -> Type.t -> texpr;
}

let create_continuation_api base_continuation_class immediate_suspension_result_class immediate_result immediate_error state result error completion context goto_label recursing = {
	base_continuation_class;
	immediate_suspension_result_class;
	immediate_result;
	immediate_error;
	state;
	result;
	error;
	completion;
	context;
	goto_label;
	recursing;
}