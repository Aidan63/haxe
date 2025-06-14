package hxcoro.ds.channels;

import haxe.coro.ICancellableContinuation;
import haxe.Exception;
import haxe.exceptions.ArgumentException;
import haxe.exceptions.CancellationException;
import haxe.coro.cancellation.CancellationToken;
import haxe.coro.context.Context;
import haxe.coro.IContinuation;
import hxcoro.Coro.suspendCancellable;
import hxcoro.ds.PagedDeque;
import hxcoro.ds.Out;
import hxcoro.ds.channels.bounded.BoundedReader;
import hxcoro.ds.channels.bounded.BoundedWriter;
import hxcoro.ds.channels.bounded.BoundedChannel;

abstract class Channel<T> {

	public final reader : IChannelReader<T>;

	public final writer : IChannelWriter<T>;

	function new(reader, writer) {
		this.reader = reader;
		this.writer = writer;
	}

	public static function createBounded(size : Int) { 
		if (size < 1) {
			throw new ArgumentException("size");
		}

		final buffer       = [];
		final readWaiters  = new PagedDeque();
		final writeWaiters = new PagedDeque();
		
		return
			new BoundedChannel(
				new BoundedReader(buffer, size, writeWaiters, readWaiters),
				new BoundedWriter(buffer, size, writeWaiters, readWaiters));
	}
}
