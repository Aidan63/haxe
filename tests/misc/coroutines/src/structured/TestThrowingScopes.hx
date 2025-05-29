package structured;

import haxe.Exception;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;
import haxe.coro.schedulers.VirtualTimeScheduler;
import haxe.exceptions.CancellationException;

class FooException extends Exception {
	public function new() {
		super('foo');
	}
}

class TestThrowingScopes extends utest.Test {
	public function test_error_passes_up() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				scope.async(_ -> {
					throw new FooException();
				});
			});
		}, FooException);
	}

	public function test_error_passes_up_deep_nesting() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				scope.async(scope -> {
					scope.async(_ -> {
						throw new FooException();
					});
				});
			});
		}, FooException);
	}

	public function test_sibling_cancelled() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				scope.async(_ -> {
					while (true) {
						yield();
					}
				});

				throw new FooException();
			});
		}, FooException);
	}

	public function test_recursive_children_cancelled_non_suspending_root() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				scope.async(scope -> {
					scope.async(scope -> {
						while (true) {
							yield();
						}
					});
				});

				throw new FooException();
			});
		}, FooException);
	}

	public function test_catching_awaiting_child() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				final child = scope.async(scope -> {
					yield();

					throw new FooException();
				});

				AssertAsync.raises(() -> child.await(), FooException);
			});
		}, FooException);
	}

	// public function test_child_throwing_cancelling_parent() {
	// 	final scheduler = new VirtualTimeScheduler();
	// 	final task      = Coroutine.with(scheduler).create(scope -> {
	// 		final child = scope.async(scope -> {
	// 			delay(1000);

	// 			throw new FooException();
	// 		});

	// 		while (true) {
	// 			yield();
	// 		}
	// 	});

	// 	task.start();

	// 	scheduler.advanceBy(1000);

	// 	Assert.isFalse(task.isActive());
	// 	Assert.isOfType(task.getError(), FooException);
	// }

	public function test_manually_cancelling_child() {
		final scheduler = new VirtualTimeScheduler();
		final task      = Coroutine.with(scheduler).create(scope -> {
			final child = scope.async(scope -> {
				delay(1000);
			});

			delay(500);

			child.cancel();
		});

		// TODO : Once eager cancellation of delay is implemented advance time by 500ms and see if we're active.
		
		task.start();

		scheduler.advanceBy(1000);

		Assert.isFalse(task.isActive());
	}

	public function test_manually_cancelling_polling_child() {
		final scheduler = new VirtualTimeScheduler();
		final task      = Coroutine.with(scheduler).create(scope -> {
			final child = scope.async(scope -> {
				while (true) {
					yield();
				}
			});

			delay(500);

			child.cancel();
		});
		
		task.start();

		scheduler.advanceBy(500);

		Assert.isFalse(task.isActive());
	}
}