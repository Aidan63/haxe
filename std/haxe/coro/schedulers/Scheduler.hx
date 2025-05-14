package haxe.coro.schedulers;

import haxe.coro.context.Key;

abstract class Scheduler {
	public static final key:Key<Scheduler> = Key.createNew('_hx_scheduler');

	public abstract function schedule(func:() -> Void):Void;

	public abstract function scheduleIn(func:() -> Void, ms:Int):Void;
}