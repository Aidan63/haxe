package haxe.exceptions;

import haxe.CallStack;

class CoroutineException extends Exception {

	final customStack:CallStack;

	public function new(message:String, previous:Exception, topStack:Array<StackItem>, coroStack:Null<CallStack>, bottomStack:CallStack) {
        super(message, previous);
		coroStack ??= [];
		customStack = topStack.concat(coroStack.asArray()).concat(bottomStack.asArray());
		this.stack = customStack;
    }

	override function get_stack():CallStack {
		return customStack;
	}
}