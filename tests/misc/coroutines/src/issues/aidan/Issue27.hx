package issues.aidan;

import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import haxe.coro.Coroutine;
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
}