package ds.channels;

import haxe.coro.context.Context;
import haxe.coro.IContinuation;
import haxe.Exception;
import haxe.exceptions.ArgumentException;
import haxe.exceptions.CancellationException;
import haxe.exceptions.NotImplementedException;
import hxcoro.ds.channels.bounded.BoundedWriter;
import hxcoro.ds.PagedDeque;
import haxe.coro.schedulers.VirtualTimeScheduler;

using hxcoro.util.Convenience;

private class TestContinuation<T> implements IContinuation<Bool> {
	final expected : Array<T>;
	final value : T;

	public var context (get, never) : Context;

	function get_context():Context {
		throw new NotImplementedException();
	}

	public function new(expected : Array<T>, value : T) {
		this.expected = expected;
		this.value    = value;
	}

	public function resume(_:Bool, _:Exception) {
		expected.push(value);
	}
}

class TestBoundedWriter extends utest.Test {
	function test_try_write_has_space() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);

		Assert.isTrue(writer.tryWrite(10));
		Assert.same([ 10 ], buffer);
	}

	function test_try_write_full_buffer() {
		final buffer        = [ 0 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);

		Assert.isFalse(writer.tryWrite(10));
		Assert.same([ 0 ], buffer);
	}

	function test_try_write_wakeup_all_readers() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final expected      = [];

		readWaiters.push(new TestContinuation(expected, '1'));
		readWaiters.push(new TestContinuation(expected, '2'));

		Assert.isTrue(writer.tryWrite(10));
		Assert.isTrue(readWaiters.isEmpty());
		Assert.same([ '1', '2' ], expected);
	}

	function test_wait_for_write_empty_buffer() {
		final buffer        = [];
		final maxBufferSize = 2;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(writer.waitForWrite());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ true ], actual);
		Assert.isTrue(writeWaiters.isEmpty());
	}

	function test_wait_for_write_partial_buffer() {
		final buffer        = [ 0 ];
		final maxBufferSize = 2;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(writer.waitForWrite());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ true ], actual);
		Assert.isTrue(writeWaiters.isEmpty());
	}

	function test_wait_for_write_full_buffer() {
		final buffer        = [ 0, 0 ];
		final maxBufferSize = 2;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(writer.waitForWrite());
		});

		task.start();

		scheduler.advanceBy(1);

		Assert.isTrue(task.isActive());
		Assert.same([], actual);
		Assert.isFalse(writeWaiters.isEmpty());
	}

	function test_wait_for_write_full_buffer_wakeup() {
		final buffer        = [ 0, 0 ];
		final maxBufferSize = 2;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(writer.waitForWrite());
		});

		task.start();

		scheduler.advanceBy(1);

		writeWaiters.pop().succeedAsync(true);

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ true ], actual);
		Assert.isTrue(writeWaiters.isEmpty());
	}

	function test_wait_for_write_full_buffer_cancellation() {
		final buffer        = [ 0, 0 ];
		final maxBufferSize = 2;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final actual        = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			actual.push(writer.waitForWrite());
		});

		task.start();

		scheduler.advanceBy(1);

		task.cancel();

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.isOfType(task.getError(), CancellationException);
		Assert.same([], actual);
		Assert.isFalse(writeWaiters.isEmpty());
	}

	// function test_wait_for_write_prompt_cancellation() {
	// 	final buffer        = [ ];
	// 	final maxBufferSize = 1;
	// 	final writeWaiters  = new PagedDeque();
	// 	final readWaiters   = new PagedDeque();
	// 	final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
	// 	final scheduler     = new VirtualTimeScheduler();
	// 	final actual        = [];
	// 	final task          = CoroRun.with(scheduler).create(node -> {
	// 		actual.push(writer.waitForWrite());
	// 	});

	// 	task.start();
	// 	task.cancel();

	// 	scheduler.advanceBy(1);

	// 	Assert.isFalse(task.isActive());
	// 	Assert.isOfType(task.getError(), CancellationException);
	// 	Assert.same([], actual);
	// 	Assert.isFalse(writeWaiters.isEmpty());
	// }

	function test_write_has_space() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			writer.write(10);
		});

		task.start();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ 10 ], buffer);
		Assert.isTrue(writeWaiters.isEmpty());
	}

	function test_write_full_buffer() {
		final buffer        = [ 10 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			writer.write(20);
		});

		task.start();
		scheduler.advanceBy(1);

		Assert.isTrue(task.isActive());
		Assert.same([ 10 ], buffer);
		Assert.isFalse(writeWaiters.isEmpty());
	}

	function test_write_wakup_all_readers() {
		final buffer        = [];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final expected      = [];
		final task          = CoroRun.with(scheduler).create(node -> {
			writer.write(10);
		});

		readWaiters.push(new TestContinuation(expected, '1'));
		readWaiters.push(new TestContinuation(expected, '2'));

		task.start();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.isTrue(readWaiters.isEmpty());
		Assert.same([ '1', '2' ], expected);
	}

	function test_write_full_buffer_wakeup() {
		final buffer        = [ 0 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			writer.write(10);
		});

		task.start();
		scheduler.advanceBy(1);

		Assert.isTrue(task.isActive());
		Assert.same([ 0 ], buffer);

		buffer.resize(0);
		writeWaiters.pop().succeedAsync(true);

		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.same([ 10 ], buffer);
	}

	function test_write_cancellation() {
		final buffer        = [ 0 ];
		final maxBufferSize = 1;
		final writeWaiters  = new PagedDeque();
		final readWaiters   = new PagedDeque();
		final writer        = new BoundedWriter(buffer, maxBufferSize, writeWaiters, readWaiters);
		final scheduler     = new VirtualTimeScheduler();
		final task          = CoroRun.with(scheduler).create(node -> {
			writer.write(10);
		});

		task.start();
		scheduler.advanceBy(1);
		task.cancel();
		scheduler.advanceBy(1);

		Assert.isFalse(task.isActive());
		Assert.isOfType(task.getError(), CancellationException);
		Assert.same([ 0 ], buffer);
		Assert.isFalse(writeWaiters.isEmpty());
	}
}