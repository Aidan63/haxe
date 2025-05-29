package structured;

import haxe.coro.schedulers.VirtualTimeScheduler;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;

class TestChildScopes extends utest.Test {
	function test_waiting_for_child() {
		var result = 0;

		Coroutine.runScoped(scope -> {
			scope.async(_ -> {
				delay(1000);

				result = 1;
			});
		});

		Assert.equals(result, 1);
	}

	function test_deeply_nested_child() {
		var result = 0;

		Coroutine.runScoped(scope -> {
			scope.async(scope -> {
				scope.async(scope -> {
					scope.async(_ -> {
						delay(1000);

						result = 1;
					});
				});
			});
		});

		Assert.equals(result, 1);
	}

	function test_waiting_for_many_children() {
		final result    = [];
		final scheduler = new VirtualTimeScheduler();
		final task      = Coroutine.with(scheduler).create(scope -> {
			scope.async(_ -> {
				delay(500);

				result.push(0);
			});

			scope.async(_ -> {
				delay(1000);

				result.push(1);
			});
		});

		task.start();

		scheduler.advanceTo(499);
		Assert.same([], result);

		scheduler.advanceTo(500);
		Assert.same([ 0 ], result);

		scheduler.advanceTo(999);
		Assert.same([ 0 ], result);

		scheduler.advanceTo(1000);
		Assert.same([ 0, 1 ], result);

		Assert.isFalse(task.isActive());
	}

	function test_waiting_for_many_nested_children() {
		final result = [];

		Coroutine.runScoped(scope -> {
			scope.async(scope -> {
				scope.async(_ -> {
					delay(500);

					result.push(0);
				});
			});

			scope.async(_ -> {
				delay(1000);

				result.push(1);
			});
		});

		Assert.same(result, [ 0, 1 ]);
	}

	function test_awaiting_child() {
		final expected = 'Hello, World';
		final result   = Coroutine.runScoped(scope -> {
			final child = scope.async(_ -> {
				delay(1000);

				return expected;
			});

			return child.await();
		});

		Assert.equals(result, expected);
	}

	function test_awaiting_nested_child() {
		final expected = 'Hello, World';
		final result   = Coroutine.runScoped(scope -> {
			final child = scope.async(scope -> {
				return
					scope
						.async(_ -> {
							delay(1000);

							return expected;
						})
						.await();

			});

			return child.await();
		});

		Assert.equals(result, expected);
	}

	function test_awaiting_single_child() {
		var result = 0;

		Coroutine.runScoped(scope -> {
			scope.async(_ -> {
				delay(500);

				result = 1;
			});

			scope
				.async(_ -> delay(1000))
				.await();
		});

		Assert.equals(result, 1);
	}

	function test_awaiting_completed_child() {
		final expected = 'Hello, World!';
		final result   = Coroutine.runScoped(scope -> {
			final child = scope.async(_ -> {
				yield();

				return expected;
			});

			delay(10);

			return child.await();
		});

		Assert.equals(expected, result);
	}
}