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

typedef DropCallback<T> = (dropped : T)->Void;

enum ChannelKind {
	Bounded(size : Int);
	Unbounded;
}

enum FullBehaviour<T> {
	Wait;
	DropNewest(f : DropCallback<T>);
	DropOldest(f : DropCallback<T>);
	DropWrite(f : DropCallback<T>);
}

typedef ChannelOptions<T> = {
	var kind : ChannelKind;

	var ?writeBehaviour : FullBehaviour<T>;

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

	public static function create<T>(options : ChannelOptions<T>):Channel<T> { 
		switch options.kind {
			case Bounded(size):
				if (size < 1) {
					throw new ArgumentException("size");
				}

				final closed         = new Out();
				final singleReader   = options.singleReader ?? false;
				final singleWriter   = options.singleWriter ?? false;
				final writeBehaviour = options.writeBehaviour ?? Wait;

				if (singleReader && singleWriter && writeBehaviour.match(DropNewest(_)) == false && writeBehaviour.match(DropOldest(_)) == false) {
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
