package haxe.coro.coroutines;

import haxe.coro.context.Key;
import haxe.coro.context.Element;

abstract class AbstractCoroutine extends Element<AbstractCoroutine> {
	public static final key : Key<AbstractCoroutine> = Key.createNew('_hx_coroutine');

	public function new() {
		super(key);
	}
}