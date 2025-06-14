package hxcoro.ds.channels;

import hxcoro.ds.Out;

interface IChannelWriter<T> {
	function tryWrite(out:T):Bool;

	@:coroutine function write(v:T):Void;

	@:coroutine function waitForWrite():Bool;

	function close():Void;
}