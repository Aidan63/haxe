package haxe.coro;

import haxe.CallStack.StackItem;
import haxe.Exception;

abstract class BaseContinuation<T> extends ContinuationResult<T> implements IContinuation<T> implements IStackFrame {
    public final _hx_completion:IContinuation<Any>;

	public final _hx_context:CoroutineContext;

    public var _hx_state:Int;

    public var _hx_recursing:Bool;

    public var _hx_stackItem:StackItem;

    function new(completion:IContinuation<Any>, initialState:Int) {
        _hx_completion = completion;
        _hx_context    = completion._hx_context;
        _hx_state      = initialState;
        _hx_error      = null;
        _hx_result     = null;
        _hx_recursing  = false;
    }

    public final function resume(result:Any, error:Exception):Void {
        _hx_result = result;
        _hx_error  = error;
        _hx_context.scheduler.schedule(() -> {
		_hx_recursing = false;

		final result = invokeResume();
			switch (result._hx_control) {
				case Pending:
					return;
				case Returned:
					_hx_completion.resume(result._hx_result, null);
				case Thrown:
					_hx_completion.resume(null, result._hx_error);
			}
        });
    }

    public function callerFrame():Null<IStackFrame> {
        return if (_hx_completion is IStackFrame) {
            cast _hx_completion;
        } else {
            null;
        }
    }

    public function setClassFuncStackItem(cls:String, func:String, file:String, line:Int, pos:Int) {
        _hx_stackItem = StackItem.FilePos(StackItem.Method(cls, func), file, line, pos);
    }

    public function setLocalFuncStackItem(id:Int, file:String, line:Int, pos:Int) {
        _hx_stackItem = StackItem.FilePos(StackItem.LocalFunction(id), file, line, pos);
    }

    abstract function invokeResume():ContinuationResult<T>;
}