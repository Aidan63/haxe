package haxe.coro;

interface ICoroutineScope {
	final context : CoroutineContext;

	function start(c : Coroutine<ICoroutineScope->Void>) : ICoroutine;
}