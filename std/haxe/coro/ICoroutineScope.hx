package haxe.coro;

import haxe.coro.context.Context;

interface ICoroutineScope {
	final context : Context;

	function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T>;
}