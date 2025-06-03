package haxe.coro;

interface ICancellableContinuation<T> extends IContinuation<T> {
	var onCancellationRequested (never, set) : ()->Void;
}