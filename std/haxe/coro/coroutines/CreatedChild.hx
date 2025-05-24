package haxe.coro.coroutines;

import haxe.coro.coroutines.BaseCoroutine.ScopedCoroutine;

// TODO: this is just here because of https://github.com/Aidan63/haxe/issues/91

class CreatedChild<T> implements ICoroutineScope.IAwaitableCoroutine<T> {
	public final parent:BaseCoroutine<Any>;
	public final child:BaseCoroutine<T>;
	public final f:ScopedCoroutine<T>;

	public function new(parent:BaseCoroutine<Any>, child:BaseCoroutine<T>, f:ScopedCoroutine<T>) {
		this.parent = parent;
		this.child = child;
		this.f = f;
	}

	@:coroutine public function await() {
		parent.startChild(child, f);
		return child.await();
	}
}
