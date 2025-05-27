package structured;

import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import haxe.coro.Coroutine.yield;
import structured.TestThrowingScopes.FooException;

class TestLazyScopes extends utest.Test {
	function test_create_return() {
		final result = Coroutine.runScoped(scope -> {
			final child = scope.lazy(_ -> return "foo");
			return child.await();
		});
		Assert.equals("foo", result);
	}

	function test_create_throw() {
		Assert.raises(() -> Coroutine.runScoped(scope -> {
			final child = scope.lazy(_ -> throw new FooException());
			AssertAsync.raises(() -> child.await(), FooException);
		}), FooException);
	}

	function test_create_unlaunched() {
		Assert.raises(() -> Coroutine.runScoped(scope -> {
			scope.lazy(_ -> {
				throw new FooException();
			});
		}), FooException);
	}

	function test_create_unlaunched_nested() {
		Assert.raises(() -> Coroutine.runScoped(scope -> {
			scope.lazy(scope -> {
				scope.lazy(scope -> {
					throw new FooException();
				});
			});
		}), FooException);
	}

	function test_create_unlaunched_yield() {
		Assert.raises(() -> Coroutine.runScoped(scope -> {
			scope.lazy(_ -> {
				yield();
				throw new FooException();
			});
		}), FooException);
	}

	function test_create_unlaunched_yield_nested() {
		Assert.raises(() -> Coroutine.runScoped(scope -> {
			scope.lazy(scope -> {
				yield();
				scope.lazy(scope -> {
					yield();
					throw new FooException();
				});
			});
		}), FooException);
	}

	function test_create_catch() {
		final result = Coroutine.runScoped(scope -> {
			try {
				Coroutine.scope(scope -> {
					final child = scope.lazy(_ -> throw new FooException());
					child.await();
				});
				return "wrong";
			} catch (exc:FooException) {
				return exc.message;
			}
		});
		Assert.equals("foo", result);
	}
}
