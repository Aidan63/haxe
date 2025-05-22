package structured;

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
				scope.start(_ -> {
					delay(500);

					actual.push(0);
				});

				scope.start(_ -> {
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
			final child = scope.start(_ -> {
				Coroutine.scope(scope -> {
					while (scope.context.get(Coroutine.key).isCancelled == false) {
						yield();
					}
					acc.push("scope 1");
				});
				// acc.push("scope 2"); // should this order be defined?
			});

			delay(1000);

			child.cancel();
			acc.push("scope 3");
		});
		Assert.equals("scope 3, scope 1", acc.join(", "));
	}
}