package haxe.coro.schedulers;

import haxe.coro.context.Key;
import haxe.coro.context.Element;

abstract class Scheduler extends Element {
	public static final key:Key<Scheduler> = Key.createNew('_hx_scheduler');

	function new() {
		super(key.id);
	}

	public abstract function schedule(func:() -> Void):Void;

	public abstract function scheduleIn(func:() -> Void, ms:Int):Void;
}