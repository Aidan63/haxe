package haxe.coro.scopes;

class SupervisorScopeComponent extends ScopeComponent {
	public function new() {}

	public function childCancels<T:ICoroutine<Any> & IContinuation<Any>>(parent:T, child:ICoroutine<Any>, error:Exception) {}

	public function childErrors<T:ICoroutine<Any> & IContinuation<Any>>(parent:T, child:ICoroutine<Any>, error:Exception) {}
}