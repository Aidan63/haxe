package haxe.coro.coroutines;

import haxe.coro.schedulers.Scheduler;
import haxe.coro.coroutines.BaseCoroutine.ScopedCoroutine;

// TODO: this is just here because of https://github.com/Aidan63/haxe/issues/91

class CreatedCoroutine<T> implements ICoroutineScope.IAwaitableCoroutine<T> {
	public final coroutine:BaseCoroutine<T>;
	public final f:ScopedCoroutine<T>;

	public function new(coroutine:BaseCoroutine<T>, f:ScopedCoroutine<T>) {
		this.coroutine = coroutine;
		this.f = f;
	}

	@:coroutine public function await() {
		coroutine.context.get(Scheduler.key).schedule(() -> {
			Coroutine.startCoroutine(coroutine, f);
		});
		return coroutine.await();
	}
}
