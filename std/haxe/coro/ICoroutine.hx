package haxe.coro;

import haxe.coro.context.Context;
import haxe.coro.coroutines.BaseCoroutine;
import haxe.exceptions.CancellationException;

interface ICoroutine<T> {

	var isCancellable(get,null):Bool;

	var isCompleted(get,null):Bool;

	@:coroutine function await() : T;

	function cancel(?error:CancellationException):Void;

	function child(context:Context) : BaseCoroutine<T>;
}