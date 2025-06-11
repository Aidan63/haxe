package ds;

import hxcoro.ds.Out;
import haxe.coro.schedulers.VirtualTimeScheduler;
import hxcoro.Coro.*;
import hxcoro.CoroRun;
import hxcoro.ds.Channel;
import haxe.ds.Option;
import hxcoro.exceptions.TimeoutException;

class TestChannel extends utest.Test {
	function test() {
		final size = 100;
		final channel = new Channel(3);
		final scheduler = new VirtualTimeScheduler();
		final task = CoroRun.with(scheduler).create(node -> {
			final output = [];
			final writer = node.async(_ -> {
				var i = size;

				while (i >= 0) {
					channel.write(i);

					i--;

					delay(Std.random(5));
				}
			});
			for (_ in 0...size + 1) {
				output.push(channel.read());
				delay(Std.random(5));
			}
			writer.cancel();
			output;
		});
		task.start();
		while (task.isActive()) {
			scheduler.run();
			scheduler.advanceBy(1);
		}
		final expected = [for (i in 0...size + 1) i];
		expected.reverse();
		Assert.same(expected, task.get());
	}

	function test_fifo_writes() {
		final actual    = [];
		final channel   = new Channel(0);
		final scheduler = new VirtualTimeScheduler();
		final task      = CoroRun.with(scheduler).create(node -> {
			node.async(_ -> {
				channel.write('Hello');
			});

			node.async(_ -> {
				channel.write('World');
			});

			delay(100);

			actual.push(channel.read());
			actual.push(channel.read());
		});

		task.start();

		scheduler.advanceBy(100);
		Assert.same([ 'Hello', 'World' ], actual);

		Assert.isFalse(task.isActive());
	}

	function test_fifo_reads() {
		final actual    = [];
		final channel   = new Channel(0);
		final scheduler = new VirtualTimeScheduler();
		final task      = CoroRun.with(scheduler).create(node -> {
			node.async(_ -> {
				actual.push(channel.read());
				actual.push(channel.read());
			});

			delay(100);

			channel.write('Hello');
			channel.write('World');
		});

		task.start();

		scheduler.advanceBy(100);
		Assert.same([ 'Hello', 'World' ], actual);

		Assert.isFalse(task.isActive());
	}

	function test_write_cancellation() {
		final actual     = [];
		final exceptions = [];
		final channel    = new Channel(0);
		final scheduler  = new VirtualTimeScheduler();
		final task       = CoroRun.with(scheduler).create(node -> {
			node.async(_ -> {
				try {
					timeout(100, _ -> {
						channel.write('Hello');
					});
				} catch (_:TimeoutException) {
					exceptions.push(scheduler.now());
				}
			});

			node.async(_ -> {
				channel.write('World');
			});

			delay(200);

			actual.push(channel.read());
		});

		task.start();

		scheduler.advanceBy(99);
		Assert.same([], actual);

		scheduler.advanceBy(1);
		Assert.same([], actual);
		Assert.equals(1, exceptions.length);
		Assert.isTrue(100i64 == exceptions[0]);

		scheduler.advanceBy(100);
		Assert.same([ 'World' ], actual);

		Assert.isFalse(task.isActive());
	}

	function test_read_cancellation() {
		final actual     = [];
		final exceptions = [];
		final channel    = new Channel(0);
		final scheduler  = new VirtualTimeScheduler();
		final task       = CoroRun.with(scheduler).create(node -> {
			node.async(_ -> {
				try {
					timeout(100, _ -> {
						return channel.read();
					});
				} catch(_:TimeoutException) {
					exceptions.push(scheduler.now());
					"";
				}
			});

			node.async(_ -> {
				actual.push(channel.read());
			});

			delay(200);

			channel.write('Hello');
		});

		task.start();

		scheduler.advanceBy(100);
		scheduler.advanceBy(100);

		Assert.same([ 'Hello' ], actual);
		Assert.equals(1, exceptions.length);
		Assert.isTrue(100i64 == exceptions[0]);
		Assert.isFalse(task.isActive());
	}

	function test_try_read() {
		final channel = new Channel(1);
		final scheduler = new VirtualTimeScheduler();
		final task = CoroRun.with(scheduler).create(node -> {
			final output = [];
			node.async(node -> {
				var out = new Out();
				function report(didRead:Bool) {
					if (didRead) {
						output.push(Some(out.get()));
					} else {
						output.push(None);
					}
				}
				// from buffer
				report(channel.tryRead(out));
				delay(2);
				report(channel.tryRead(out));
				report(channel.tryRead(out));

				// from suspense
				delay(2);
				report(channel.tryRead(out));
				report(channel.tryRead(out));
				report(channel.tryRead(out));
			});
			delay(1);
			channel.write(1);
			delay(2);
			channel.write(2);
			channel.write(3);
			output;
		});
		task.start();
		while (task.isActive()) {
			scheduler.run();
			scheduler.advanceBy(1);
		}
		Assert.same([None, Some(1), None, Some(2), Some(3), None], task.get());
	}

	var todoHoisting = 0;

	function test_iterator() {
		final size = 50;
		for (bufferSize in [0, 1, 25, 50]) {
			todoHoisting = 0;
			final channel = new Channel(bufferSize);
			final scheduler = new VirtualTimeScheduler();
			final task = CoroRun.with(scheduler).create(node -> {
				for (i in 0...size) {
					node.async(_ -> channel.write(todoHoisting++));
				}
				delay(1);
				final res = [for (i in channel) i];
				res;
			});
			task.start();
			while (task.isActive()) {
				scheduler.run();
				scheduler.advanceBy(1);
			}
			Assert.same([for (i in 0...size) i], task.get());
		}
	}
}