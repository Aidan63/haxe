package haxe.coro.coroutines;

import haxe.coro.context.Context;

class ChildCoroutine<T> extends BaseCoroutine<T> {
	public function new(parentContext : Context) {
		final ctx    = parentContext.clone();
		final parent = parentContext.get(AbstractCoroutine.key);

		super(ctx, (cast parent : ICoroutine<Any>));

		ctx.add(this);
	}
}