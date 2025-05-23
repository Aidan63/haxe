package haxe.coro.scopes;

interface IScopeComponent {
	function childCancels<T:ICoroutine<Any> & IContinuation<Any>>(parent:T, child:ICoroutine<Any>, error:Exception):Void;

	function childErrors<T:ICoroutine<Any> & IContinuation<Any>>(parent:T, child:ICoroutine<Any>, error:Exception):Void;
}