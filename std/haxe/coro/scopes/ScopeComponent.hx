package haxe.coro.scopes;

import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import haxe.coro.coroutines.BaseCoroutine;

abstract class ScopeComponent implements IElement<ScopeComponent> {
	public static final key:Key<ScopeComponent> = Key.createNew('Scope');

	abstract public function cancel(coroutine:BaseCoroutine<Any>):Void;
	abstract public function onCompletion(coroutine:BaseCoroutine<Any>, childCoroutine:BaseCoroutine<Any>):Void;

	public function getKey() {
		return key;
	}
}