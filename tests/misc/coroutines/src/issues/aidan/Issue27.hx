package issues.aidan;

import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;
import hxcoro.ICoroScope;

class DebugName implements IElement<DebugName> {
	static public var key:Key<DebugName> = Key.createNew("DebugName");

	public var name:String;

	public function new(name:String) {
		this.name = name;
	}

	public function getKey() {
		return key;
	}

	public function toString() {
		return '[DebugName: $name]';
	}
}

class ImpatientScheduler extends Scheduler {

	public function new() {
		super();
	}

	public function schedule(func:() -> Void) {
		func();
	}

	public function scheduleIn(func:() -> Void, _) {
		func();
	}

	public function tick() {
		return true;
	}
}

class Issue27 extends utest.Test {
	@:coroutine
	function logDebug() {
		return Coroutine.suspend(cont -> {
			cont.resume(cont.context.get(DebugName.key).name, null);
		});
	}

	@:coroutine
	function modifyDebug(name:String) {
		Coroutine.suspend(cont -> {
			cont.context.get(DebugName.key).name = name;
			cont.resume(null, null);
		});
	}

	function test() {
		Coroutine.runScoped(scope ->  {
			scope.with(new DebugName("first name")).async(_ -> {
				Assert.equals("first name", logDebug());
				modifyDebug("second name");
				Assert.equals("second name", logDebug());
			});
		});
	}

	function testScope() {
		Coroutine.runScoped(scope -> {
			scope.with(new DebugName("first name")).async(_ -> {
				Coroutine.scope(_ -> {
					Assert.equals("first name", logDebug());
					modifyDebug("second name");
					Assert.equals("second name", logDebug());
				});
			});
		});
	}

	function testEntrypoint() {
		Coroutine.with(new DebugName("first name")).run(scope -> {
			Assert.equals("first name", logDebug());
			modifyDebug("second name");
			Assert.equals("second name", logDebug());
		});

		Coroutine
			.with(new DebugName("wrong name"))
			.with(new DebugName("first name"))
			.run(scope -> {
				Assert.equals("first name", logDebug());
				modifyDebug("second name");
				Assert.equals("second name", logDebug());
		});
	}

	function testSchedulerReplacement() {
		// this isn't really a test because it would still pass with the standard Scheduler... eventually
		final result = Coroutine.with(new ImpatientScheduler()).run(_ -> {
			delay(10000000);
			"done";
		});
		Assert.equals("done", result);
	}
}