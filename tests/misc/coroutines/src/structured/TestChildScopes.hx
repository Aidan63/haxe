package structured;

import haxe.coro.scopes.SupervisorScopeComponent;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;
import structured.TestThrowingScopes.FooException;

class TestChildScopes extends utest.Test {
	function test_waiting_for_child() {
		var result = 0;

		Coroutine.runScoped(scope -> {
			scope.start(_ -> {
				delay(1000);

				result = 1;
			});
		});

		Assert.equals(result, 1);
	}

	function test_deeply_nested_child() {
		var result = 0;

		Coroutine.runScoped(scope -> {
			scope.start(scope -> {
				scope.start(scope -> {
					scope.start(_ -> {
						delay(1000);

						result = 1;
					});
				});
			});
		});

		Assert.equals(result, 1);
	}

	function test_waiting_for_many_children() {
		final result = [];

		Coroutine.runScoped(scope -> {
			scope.start(_ -> {
				delay(500);

				result.push(0);
			});

			scope.start(_ -> {
				delay(1000);

				result.push(1);
			});
		});

		Assert.same(result, [ 0, 1 ]);
	}

	function test_waiting_for_many_nested_children() {
		final result = [];

		Coroutine.runScoped(scope -> {
			scope.start(scope -> {
				scope.start(_ -> {
					delay(500);

					result.push(0);
				});
			});

			scope.start(_ -> {
				delay(1000);

				result.push(1);
			});
		});

		Assert.same(result, [ 0, 1 ]);
	}

	function test_awaiting_child() {
		final expected = 'Hello, World';
		final result   = Coroutine.runScoped(scope -> {
			final child = scope.start(_ -> {
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
			final child = scope.start(scope -> {
				return
					scope
						.start(_ -> {
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
			scope.start(_ -> {
				delay(500);

				result = 1;
			});

			scope
				.start(_ -> delay(1000))
				.await();
		});

		Assert.equals(result, 1);
	}

	function test_awaiting_completed_child() {
		final expected = 'Hello, World!';
		final result   = Coroutine.runScoped(scope -> {
			final child = scope.start(_ -> {
				yield();

				return expected;
			});

			delay(10);

			return child.await();
		});

		Assert.equals(expected, result);
	}

	function test_supervisor_scope() {
		final result = Coroutine.runScoped(scope -> {
			scope.with(new SupervisorScopeComponent()).start(scope -> {
				scope.start(_ -> throw "immediately");
				scope.start(_ -> { yield(); throw "after yield"; });
				"this is fine";
			}).await();
		});
		Assert.equals("this is fine", result);
	}

	function test_supervisor_scope_await() {
		Assert.raises(() -> Coroutine.runScoped(scope -> {
			scope.with(new SupervisorScopeComponent()).start(scope -> {
				final child = scope.start(_ -> throw new FooException());
				AssertAsync.raises(() -> child.await(), FooException);
			}).await();
		}), FooException);
	}
}