package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import hxcoro.task.AbstractTask;
import hxcoro.task.CoroTask;

interface INodeStrategy {
	function complete<T>(task:CoroTask<T>):Void;
	function childrenCompleted<T>(task:CoroTask<T>):Void;
	function childSucceeds<T>(task:CoroTask<T>, child:AbstractTask):Void;
	function childErrors<T>(task:CoroTask<T>, child:AbstractTask, cause:Exception):Void;
	function childCancels<T>(task:CoroTask<T>, child:AbstractTask, cause:CancellationException):Void;
}
