package haxe.coro;

import haxe.Exception;
import haxe.coro.context.CoroutineContext;

interface IContinuation<T> {
	final _hx_context:CoroutineContext;

	function resume(result:T, error:Exception):Void;
}
