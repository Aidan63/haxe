package haxe.coro;

import haxe.exceptions.NotImplementedException;

interface ICoroutine {
	final parent : Null<ICoroutine>;

	final children : Array<ICoroutine>;

	@:coroutine function await() : Void;
}