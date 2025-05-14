package haxe.coro.coroutines;

class ChildCoroutine<T> extends BaseCoroutine<T> {
	public function new(parentContext : CoroutineContext) {
		super(new CoroutineContext(parentContext.scheduler, this), parentContext.coroutine);
	}
}