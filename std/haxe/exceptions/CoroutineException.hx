package haxe.exceptions;

class CoroutineException extends Exception {

	final customStack:CallStack;

	public function new(message:String, previous:Exception, coroStack:CallStack, callStack:CallStack) {
        super(message, previous);
		customStack = coroStack.asArray().concat(callStack.asArray());
		this.stack = customStack;
    }

	override function get_stack():CallStack {
		return customStack;
	}
}