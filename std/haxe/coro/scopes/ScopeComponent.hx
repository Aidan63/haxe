package haxe.coro.scopes;

import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import haxe.coro.coroutines.BaseCoroutine;

abstract class ScopeComponent implements IScopeComponent implements IElement<IScopeComponent> {
	public static final key:Key<IScopeComponent> = Key.createNew('Scope');

	public function getKey() {
		return key;
	}
}