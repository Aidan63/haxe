package ds.channels;

import haxe.exceptions.ArgumentException;
import haxe.exceptions.CancellationException;
import hxcoro.ds.channels.bounded.BoundedWriter;
import hxcoro.ds.PagedDeque;
import haxe.coro.schedulers.VirtualTimeScheduler;

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

		writeWaiters.pop().resume(true, null);

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
}