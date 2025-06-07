package haxe.coro.schedulers;

import haxe.coro.context.Key;
import haxe.coro.context.IElement;

abstract class Scheduler implements IElement<Scheduler> {
	public static final key = new Key<Scheduler>('Scheduler');

	function new() {}

	public abstract function schedule<T>(ms:Int64, state:T, func:(scheduler:Scheduler, state:T) -> Void):ISchedulerHandle;

	public abstract function now():Int64;

	public function getKey() {
		return key;
	}
}
