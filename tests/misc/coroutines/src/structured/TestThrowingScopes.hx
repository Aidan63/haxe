package structured;

import haxe.Exception;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;
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
				scope.start(_ -> {
					throw new FooException();
				});
			});
		}, FooException);
	}

	public function test_error_passes_up_deep_nesting() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				scope.start(scope -> {
					scope.start(_ -> {
						throw new FooException();
					});
				});
			});
		}, FooException);
	}

	public function test_sibling_cancelled() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				scope.start(_ -> {
					while (scope.context.get(Coroutine.key).isCompleted == false) {
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
				scope.start(scope -> {
					scope.start(scope -> {
						while (scope.context.get(Coroutine.key).isCompleted == false) {
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
				final child = scope.start(scope -> {
					yield();

					throw new FooException();
				});

				AssertAsync.raises(() -> child.await(), FooException);
			});
		}, FooException);
	}

	public function test_child_throwing_cancelling_parent() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				final child = scope.start(scope -> {
					delay(1000);

					throw new FooException();
				});

				while (scope.context.get(Coroutine.key).isCompleted == false) {
					yield();
				}
			});
		}, FooException);
	}

	public function test_manually_cancelling_child() {
		Coroutine.runScoped(scope -> {
			final child = scope.start(scope -> {
				delay(1000);
			});

			delay(500);

			child.cancel();
			Assert.pass();
		});
	}

	public function test_manually_cancelling_polling_child() {
		Coroutine.runScoped(scope -> {
			final child = scope.start(scope -> {
				while (scope.context.get(Coroutine.key).isCompleted == false) {
					yield();
				}
			});

			delay(500);

			child.cancel();
			Assert.pass();
		});
	}

	public function test_catching_child_throw() {
		final result = Coroutine.runScoped(scope -> {
			final child = scope.start(_ -> {
				yield();
				throw new FooException();
			});
			try {
				child.await();
				"not caught";
			} catch(e:FooException) {
				"caught";
			}
		});
		Assert.equals("caught", result);
	}

	public function test_catching_child_throw_but_still_throwing() {
		Assert.raises(() ->
			Coroutine.runScoped(scope -> {
				final child = scope.start(_ -> {
					yield();
					throw new FooException();
				});
				final child2 = scope.start(_ -> {
					yield();
					child.await();
				});
				/* The parent itself catches child's exception, but because
				   child2 doesn't the parent will receive the exception from
				   it and throw accordingly.
				*/
				try {
					child.await();
				} catch (e:FooException) {}
			})
		, FooException);
	}

	public function test_catching_multiple_awaits() {
		var counter = 0;
		final result = Coroutine.runScoped(scope -> {
			final child = scope.start(_ -> {
				yield();
				throw new FooException();
			});
			for (i in 0...5) {
				scope.start(_ -> {
					try {
						child.await();
					} catch (e:FooException) {
						counter++;
					}
				});
			}
			try {
				child.await();
				"not caught";
			} catch(e:FooException) {
				"caught";
			}
		});
		Assert.equals("caught", result);
		Assert.equals(5, counter);
	}
}