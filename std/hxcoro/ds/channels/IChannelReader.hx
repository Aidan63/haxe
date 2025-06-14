package hxcoro.ds.channels;

import hxcoro.ds.Out;

interface IChannelReader<T> {
	function tryRead(out:Out<T>):Bool;

	@:coroutine function read():T;

	@:coroutine function waitForRead():Bool;
}