package haxe.coro;

import haxe.coro.context.Context;
import haxe.coro.coroutines.BaseCoroutine;

interface ICoroutine<T> {
	var isRunning (get, never) : Bool;

	var isCancelled (get, never) : Bool;

	var isCompleted (get, never) : Bool;

	@:coroutine function await() : T;

	function cancel() : Void;

	function child(context:Context) : BaseCoroutine<T>;
}