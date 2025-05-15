package haxe.coro.coroutines;

import haxe.coro.context.Context;

class ChildCoroutine<T> extends BaseCoroutine<T> {
	public function new(parentContext : Context) {
		final ctx    = parentContext.clone();
		final parent = parentContext.get(Coroutine.key);

		super(ctx, parent);

		ctx.add(this);
	}
}