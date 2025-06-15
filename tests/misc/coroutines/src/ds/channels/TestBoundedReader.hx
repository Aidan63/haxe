package ds.channels;

import haxe.Exception;
import haxe.coro.IContinuation;
import haxe.coro.context.Context;
import haxe.coro.schedulers.VirtualTimeScheduler;
import haxe.exceptions.ArgumentException;
import haxe.exceptions.CancellationException;
import haxe.exceptions.NotImplementedException;
import hxcoro.exceptions.ChannelClosedException;
import hxcoro.ds.Out;
import hxcoro.ds.PagedDeque;
import hxcoro.ds.channels.bounded.BoundedReader;

using hxcoro.util.Convenience;

private class TestContinuation<T> implements IContinuation<Bool> {
	final actual : Array<T>;
	final value : T;

	public var context (get, never) : Context;

	function get_context():Context {
		return Context.create(new ImmediateScheduler());
	}

	public function new(actual : Array<T>, value : T) {
		this.actual = actual;
		this.value  = value;
	}

	public function resume(_:Bool, _:Exception) {
		actual.push(value);
	}
}

class TestBoundedReader extends utest.Test {
	function test_try_read_has_data() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();

		Assert.isTrue(reader.tryRead(out));
		Assert.equals(10, out.get());
		Assert.same([], buffer);
	}

	function test_try_read_empty() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();

		Assert.isFalse(reader.tryRead(out));
		Assert.same([], buffer);
	}

	function test_try_read_wakup_all_writers() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final actual        = [];

		writeWaiters.push(new TestContinuation(actual, '1'));
		writeWaiters.push(new TestContinuation(actual, '2'));

		Assert.isTrue(reader.tryRead(out));
		Assert.isTrue(writeWaiters.isEmpty());
		Assert.same([ '1', '2' ], actual);
	}

	function test_wait_for_read_has_data() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.waitForRead());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ true ], actual);
		Assert.isTrue(readWaiters.isEmpty());
	}

	function test_wait_for_read_empty_buffer() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.waitForRead());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isTrue(task.isActive());
		Assert.same([], actual);
		Assert.same([], buffer);
		Assert.isFalse(readWaiters.isEmpty());
	}

	function test_wait_for_read_empty_buffer_wakeup() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.waitForRead());
		});

		task.start();

		scheduler.advanceBy(1);

		readWaiters.pop().succeedAsync(true);

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ true ], actual);
		Assert.isTrue(readWaiters.isEmpty());
	}

	function test_wait_for_write_empty_buffer_cancellation() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.waitForRead());
		});

		task.start();

		scheduler.advanceBy(1);

		task.cancel();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.isOfType(task.getError(), CancellationException);
		Assert.same([], actual);
		Assert.isFalse(readWaiters.isEmpty());
	}

	function test_read_has_data() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.read());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ 10 ], actual);
		Assert.same([], buffer);
		Assert.isTrue(readWaiters.isEmpty());
	}

	function test_read_empty_buffer() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.read());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isTrue(task.isActive());
		Assert.same([], buffer);
		Assert.same([], actual);
		Assert.isFalse(readWaiters.isEmpty());
	}

	function test_read_wakup_all_writers() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			reader.read();
		});

		writeWaiters.push(new TestContinuation(actual, '1'));
		writeWaiters.push(new TestContinuation(actual, '2'));

		task.start();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.isTrue(writeWaiters.isEmpty());
		Assert.same([ '1', '2' ], actual);
	}

	function test_read_empty_buffer_wakeup() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.read());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isTrue(task.isActive());
		Assert.same([], buffer);

		buffer.push(10);
		readWaiters.pop().succeedAsync(true);

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ 10 ], actual);
		Assert.same([], buffer);
	}

	function test_read_cancellation() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, new Out());
		final out           = new Out();
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.read());
		});

		task.start();
		scheduler.advanceBy(1);
		task.cancel();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.isOfType(task.getError(), CancellationException);
		Assert.same([], buffer);
		Assert.isFalse(readWaiters.isEmpty());
	}

	function test_wait_for_read_when_closed() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final closed        = new Out();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, closed);
		final actual        = [];
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.waitForRead());
		});

		closed.set(true);

		task.start();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ false ], actual);
	}

	function test_wait_for_read_when_closed_with_remaining_data() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final closed        = new Out();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, closed);
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.waitForRead());
		});

		closed.set(true);

		task.start();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ true ], actual);
	}

	function test_try_read_when_closed() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final closed        = new Out();
		final out           = new Out();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, closed);

		closed.set(true);

		Assert.isFalse(reader.tryRead(out));
	}

	function test_try_read_when_closed_with_remaining_data() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final closed        = new Out();
		final out           = new Out();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, closed);

		closed.set(true);

		Assert.isTrue(reader.tryRead(out));
		Assert.same([], buffer);
		Assert.equals(10, out.get());
	}

	function test_read_when_closed() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final closed        = new Out();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, closed);
		final actual        = [];
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			AssertAsync.raises(reader.read(), ChannelClosedException);
		});

		closed.set(true);

		task.start();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([], actual);
	}

	function test_read_when_closed_with_remaining_data() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final closed        = new Out();
		final reader        = new BoundedReader(buffer, maxBufferSize, writeWaiters, readWaiters, closed);
		final actual        = [];
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(reader.read());
		});

		closed.set(true);

		task.start();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ 10 ], actual);
	}
}