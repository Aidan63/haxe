package haxe.coro;

interface ICoroutine<T> {
	final parent : Null<ICoroutine<Any>>;

	final children : Array<ICoroutine<Any>>;

	var isRunning (get, never) : Bool;

	var isCancelled (get, never) : Bool;

	var isCompleted (get, never) : Bool;

	@:coroutine function await() : T;

	function cancel(cause : Exception) : Void;
}