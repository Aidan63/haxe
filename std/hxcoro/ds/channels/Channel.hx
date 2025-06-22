package hxcoro.ds.channels;

import haxe.coro.IContinuation;
import haxe.exceptions.ArgumentException;
import haxe.exceptions.NotImplementedException;
import hxcoro.ds.Out;
import hxcoro.ds.PagedDeque;
import hxcoro.ds.channels.bounded.BoundedReader;
import hxcoro.ds.channels.bounded.BoundedWriter;
import hxcoro.ds.channels.bounded.SingleBoundedReader;
import hxcoro.ds.channels.bounded.SingleBoundedWriter;
import hxcoro.ds.channels.bounded.BoundedChannel;
import hxcoro.concurrent.AtomicObject;

enum ChannelKind {
	Bounded(size : Int);
	Unbounded;
}

enum abstract FullBehaviour(Int) {
	var Wait;
	var DropNewest;
	var DropOldest;
	var DropWrite;
}

typedef ChannelOptions = {
	var kind : ChannelKind;

	var ?writeBehaviour : FullBehaviour;

	var ?singleReader : Bool;

	var ?singleWriter : Bool;
}

abstract class Channel<T> {

	public final reader : IChannelReader<T>;

	public final writer : IChannelWriter<T>;

	function new(reader, writer) {
		this.reader = reader;
		this.writer = writer;
	}

	public static function create<T>(options : ChannelOptions):Channel<T> { 
		switch options.kind {
			case Bounded(size):
				if (size < 1) {
					throw new ArgumentException("size");
				}
				
				final closed         = new Out();
				final singleReader   = options.singleReader ?? false;
				final singleWriter   = options.singleWriter ?? false;
				final writeBehaviour = options.writeBehaviour ?? Wait;

				if (singleReader && singleWriter && writeBehaviour != DropNewest && writeBehaviour != DropOldest) {
					final buffer      = new ConcurrentCircularBuffer(size);
					final readWaiter  = new AtomicObject<IContinuation<Bool>>(null);
					final writeWaiter = new AtomicObject<IContinuation<Bool>>(null);
					
					return
						new BoundedChannel(
							new SingleBoundedReader(buffer, writeWaiter, readWaiter, closed),
							new SingleBoundedWriter(buffer, writeWaiter, readWaiter, closed, writeBehaviour));
				} else {
					final buffer       = [];
					final readWaiters  = new PagedDeque();
					final writeWaiters = new PagedDeque();

					return
						new BoundedChannel(
							new BoundedReader(buffer, size, writeWaiters, readWaiters, closed),
							new BoundedWriter(buffer, size, writeWaiters, readWaiters, closed, writeBehaviour));
				}

			case Unbounded:
				throw new NotImplementedException();
		}
	}
}
