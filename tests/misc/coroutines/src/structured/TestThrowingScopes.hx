package structured;

import haxe.Exception;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;
import haxe.exceptions.CancellationException;

private class FooException extends Exception {
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
					while (scope.context.get(Coroutine.key).isCancelled == false) {
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
						while (scope.context.get(Coroutine.key).isCancelled == false) {
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

				while (scope.context.get(Coroutine.key).isCancelled == false) {
					yield();
				}
			});
		}, FooException);
	}

	public function test_manually_cancelling_child() {
		Assert.raises(() -> {
			Coroutine.runScoped(scope -> {
				final child = scope.start(scope -> {
					delay(1000);
				});

				delay(500);

				child.cancel();
			});
		}, CancellationException);
	}
}