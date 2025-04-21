package haxe.exceptions;

class CoroutineException extends Exception {
    final coroStack:CallStack;

    public function new(message:String, previous:Exception, coroStack:CallStack) {
        super(message, previous);

        this.coroStack = coroStack;
    }

    override function get_stack():CallStack {
        return coroStack;
    }
}