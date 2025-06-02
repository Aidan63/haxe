package haxe.coro;

interface ICancellingContinuation<T> extends IContinuation<T> {
	var onCancellationRequested (never, set) : ()->Void;
}