package hxcoro;

import haxe.exceptions.CancellationException;
import hxcoro.ICoroTask;

interface ICoroScope {
	function async<T>(lambda:ScopedLambda<T>):ICoroTask<T>;
	function lazy<T>(lambda:ScopedLambda<T>):IStartableCoroTask<T>;
	function cancel(?cause:CancellationException):Void;
}
