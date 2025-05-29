import haxe.Exception;
import haxe.coro.Coroutine.yield;
import haxe.coro.Coroutine.delay;
import haxe.coro.schedulers.VirtualTimeScheduler;

class TestBasic extends utest.Test {
	function testSimple() {
		Assert.equals(42, Coroutine.run(@:coroutine function run() {
			return simple(42);
		}));
	}

	function testErrorDirect() {
		Assert.raises(() -> Coroutine.run(error), String);
	}

	function testErrorPropagation() {
		@:coroutine function propagate() {
			error();
		}

		Assert.raises(() -> Coroutine.run(propagate), String);
	}

	function testResumeWithError() {
		@:coroutine function foo() {
			Coroutine.suspend(cont -> {
				cont.resume(null, new Exception(""));
			});
		}

		Assert.raises(() -> Coroutine.run(foo), Exception);
	}

	function testUnnamedLocalCoroutines() {
		final c1 = @:coroutine function () {
			yield();

			return 10;
		};

		Assert.equals(10, Coroutine.run(c1));
	}

	function testLocalTypeParameters() {
		Coroutine.run(@:coroutine function f<T>():T {
			return null;
		});
		Assert.pass(); // The test is that this doesn't cause an unbound type parameter
	}

	#if sys

	function testDelay() {
		final scheduler = new VirtualTimeScheduler();
		final task      = Coroutine.with(scheduler).create(_ -> {
			delay(500);
		});

		task.start();

		scheduler.advanceTo(499);
		Assert.isTrue(task.isActive());
		
		scheduler.advanceTo(500);
		Assert.isFalse(task.isActive());
	}

	#end

	@:coroutine static function simple(arg:Int):Int {
		return arg;
	}

	@:coroutine static function error() {
		throw "nope";
	}
}
