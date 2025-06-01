package ds;

import haxe.coro.schedulers.VirtualTimeScheduler;
import hxcoro.Coro.*;
import hxcoro.CoroRun;
import hxcoro.ds.Channel;
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

	function test_write_cancellation() {
		final expected  = [];
		final channel   = new Channel(0);
		final scheduler = new VirtualTimeScheduler();
		final task      = CoroRun.with(scheduler).create(node -> {
			node.async(_ -> {
				AssertAsync.raises(() -> {
					timeout(100, _ -> {
						channel.write('Hello');
					});
				}, TimeoutException);
			});

			node.async(_ -> {
				channel.write('World');
			});

			node.async(_ -> {
				delay(200);

				expected.push(channel.read());
			});
		});

		task.start();

		scheduler.advanceBy(99);
		Assert.same([], expected);

		scheduler.advanceBy(1);
		Assert.same([], expected);

		scheduler.advanceBy(100);
		Assert.same([ 'World' ], expected);

		Assert.isFalse(task.isActive());
	}
}