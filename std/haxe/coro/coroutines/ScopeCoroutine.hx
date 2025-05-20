package haxe.coro.coroutines;

import haxe.coro.context.Context;

class ScopeCoroutine<T> extends BaseCoroutine<T> {
	public function new(parentContext : Context) {
		super(parentContext.clone());

		context.add(this);
	}
}