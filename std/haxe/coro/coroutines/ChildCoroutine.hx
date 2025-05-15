package haxe.coro.coroutines;

import haxe.coro.context.Context;

class ChildCoroutine<T> extends BaseCoroutine<T> {
	public function new(parentContext : Context) {
		super(parentContext.clone(), parentContext.get(Coroutine.key));

		context.add(this);
	}
}