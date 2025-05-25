package haxe.coro;

import haxe.exceptions.CancellationException;
import haxe.coro.Coroutine.ScopedCoroutine;

interface ICoroutine<T> {

	var isCancellable(get,null):Bool;

	var isCompleted(get,null):Bool;

	@:coroutine function await() : T;

	function cancel(?error:CancellationException):Void;

	function create<T>(lambda:ScopedCoroutine<T>) : ICoroutine<T>;

	function start<T>(lambda:ScopedCoroutine<T>) : ICoroutine<T>;
}