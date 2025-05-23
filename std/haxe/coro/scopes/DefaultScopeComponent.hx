package haxe.coro.scopes;

class DefaultScopeComponent extends ScopeComponent {
	public function new() {}

	public function childCancels<T:ICoroutine<Any> & IContinuation<Any>>(parent:T, child:ICoroutine<Any>, error:Exception) {}

	public function childErrors<T:ICoroutine<Any> & IContinuation<Any>>(parent:T, child:ICoroutine<Any>, error:Exception) {
		if (parent.isCancellable) {
			parent.resume(null, error);
		}
	}
}