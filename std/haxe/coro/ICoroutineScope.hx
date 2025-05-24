package haxe.coro;

import haxe.coro.coroutines.BaseCoroutine;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;

interface IAwaitableCoroutine<T> {
	@:coroutine function await():T;
}

interface ICoroutineScope {
	final context : Context;

	function create<T>(c : Coroutine<ICoroutineScope->T>) : IAwaitableCoroutine<T>;
	function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T>;
	public function with<T>(...elements:IElement<Any>):AdjustedContext<T>;
}