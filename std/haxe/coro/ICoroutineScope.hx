package haxe.coro;

interface ICoroutineScope {
	final context : CoroutineContext;

	function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T>;
}