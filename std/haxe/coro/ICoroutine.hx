package haxe.coro;

interface ICoroutine<T> {
	final parent : Null<ICoroutine<Any>>;

	final children : Array<ICoroutine<Any>>;

	@:coroutine function await() : T;
}