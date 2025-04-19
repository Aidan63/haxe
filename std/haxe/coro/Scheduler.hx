package haxe.coro;

import haxe.coro.context.Key;
import haxe.coro.context.Element;

abstract class Scheduler extends Element<Scheduler> {
    private static final key_id = '_hx_coro_scheduler';

	public static final key = new Key<Scheduler>(key_id);

    public function new() {
		super(key_id);
	}

    public abstract function schedule(func:() -> Void):Void;
    public abstract function scheduleIn(func:() -> Void, ms:Int):Void;
}