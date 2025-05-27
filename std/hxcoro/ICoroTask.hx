package hxcoro;

import haxe.exceptions.CancellationException;

interface ICoroTask<T> {
	function cancel(?cause:CancellationException):Void;
	@:coroutine function await():T;
	function get():T;
}

interface IStartableCoroTask<T> extends ICoroTask<T> {
	function start():Void;
}
