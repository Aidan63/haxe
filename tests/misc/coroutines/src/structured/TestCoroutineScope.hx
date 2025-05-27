package structured;

import haxe.exceptions.CancellationException;
import haxe.Exception;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;

private class FooException extends Exception {
	public function new() {
		super('foo');
	}
}

class TestCoroutineScope extends utest.Test {
	function test_scope_returning_value_suspending() {
		final expected = 'Hello, World';
		final actual   = Coroutine.runScoped(_ -> {
			return Coroutine.scope(_ -> {
				yield();

				return expected;
			});
		});

		Assert.equals(expected, actual);
	}

	function test_scope_throwing_suspending() {
		Coroutine.runScoped(_ -> {
			AssertAsync.raises(() -> Coroutine.runScoped(_ -> {
				yield();

				throw new FooException();
			}), FooException);
		});
	}

	function test_scope_with_children() {
		Coroutine.runScoped(_ -> {
			final actual = [];

			Coroutine.scope(scope -> {
				scope.async(_ -> {
					delay(500);

					actual.push(0);
				});

				scope.async(_ -> {
					delay(500);

					actual.push(1);
				});
			});

			Assert.same(actual, [ 0, 1 ]);
		});
	}

	function test_parent_scope_cancelling() {
		final acc = [];
		Coroutine.runScoped(scope -> {
			final child = scope.async(_ -> {
				try {
					Coroutine.scope(scope -> {
						while (true) {
							yield();
						}
						acc.push("scope 1");
					});
				} catch (e:CancellationException) {
					acc.push("scope 2");
				}
			});

			delay(1000);
			child.cancel();
			acc.push("scope 3");
		});
		Assert.contains("scope 2", acc);
		Assert.contains("scope 3", acc);
	}
}