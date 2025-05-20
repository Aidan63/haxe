package haxe.coro;

interface ICoroutine<T> {
	var isRunning (get, never) : Bool;

	var isCancelled (get, never) : Bool;

	var isCompleted (get, never) : Bool;

	@:coroutine function await() : T;

	function cancel() : Void;
}