package hxcoro;

import haxe.coro.Coroutine;

typedef ScopedLambda<T> = Coroutine<(scope:ICoroScope) -> T>;
