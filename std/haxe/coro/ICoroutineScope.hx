package haxe.coro;

import haxe.coro.coroutines.BaseCoroutine;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;

interface ICoroutineScope {
	final context : Context;

	function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T>;
	public function with<T>(...elements:IElement<Any>):AdjustedContext<T>;
}