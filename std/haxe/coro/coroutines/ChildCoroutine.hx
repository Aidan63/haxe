package haxe.coro.coroutines;

class ChildCoroutine extends AbstractCoroutine<Any> {
	public function new(parentContext : CoroutineContext) {
		super(new CoroutineContext(parentContext.scheduler, this), parentContext.coroutine);
	}
}