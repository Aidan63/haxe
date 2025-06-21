package hxcoro.ds.channels;

import haxe.exceptions.ArgumentException;
import haxe.exceptions.NotImplementedException;
import hxcoro.ds.Out;
import hxcoro.ds.PagedDeque;
import hxcoro.ds.channels.bounded.BoundedReader;
import hxcoro.ds.channels.bounded.BoundedWriter;
import hxcoro.ds.channels.bounded.BoundedChannel;

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
		
				final buffer       = [];
				final readWaiters  = new PagedDeque();
				final writeWaiters = new PagedDeque();
				final closed       = new Out();
				
				return
					new BoundedChannel(
						new BoundedReader(buffer, size, writeWaiters, readWaiters, closed),
						new BoundedWriter(buffer, size, writeWaiters, readWaiters, closed, options.writeBehaviour ?? Wait));
			case Unbounded:
				throw new NotImplementedException();
		}
	}
}
