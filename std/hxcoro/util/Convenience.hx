package hxcoro.util;

import haxe.coro.schedulers.ISchedulerHandle;
import haxe.Int64;
import haxe.coro.schedulers.Scheduler;
import haxe.Exception;
import haxe.coro.IContinuation;

/**
	A set of convenience functions for working with hxcoro data.
**/
class Convenience {
	/**
		Resumes `cont` with `result` immediately.
	**/
	static public inline function succeedSync<T>(cont:IContinuation<T>, result:T) {
		cont.resume(result, null);
	}

	/**
		Resumes `cont` with exception `error` immediately.
	**/
	static public inline function failSync<T>(cont:IContinuation<T>, error:Exception) {
		cont.resume(null, error);
	}

	/**
		Schedules `cont` to be resumed with `result`.

		Scheduled functions do not increase the call stack and might be executed in a different
		thread if the current dispatcher allows that.
	**/
	static public inline function succeedAsync<T>(cont:IContinuation<T>, result:T) {
		resumeAsync(cont, result, null);
	}

	/**
		Schedules `cont` to be resumed with exception `error`.

		Scheduled functions do not increase the call stack and might be executed in a different
		thread if the current dispatcher allows that.
	**/
	static public inline function failAsync<T>(cont:IContinuation<T>, error:Exception) {
		resumeAsync(cont, null, error);
	}

	/**
		Calls `cont` without any values immediately.
	**/
	static public inline function callSync<T>(cont:IContinuation<T>) {
		cont.resume(null, null);
	}

	/**
		Schedules `cont` to be resumed without any values.

		Scheduled functions do not increase the call stack and might be executed in a different
		thread if the current dispatcher allows that.
	**/
	static public inline function callAsync<T>(cont:IContinuation<T>) {
		resumeAsync(cont, null, null);
	}

	/**
		Schedules `cont` to be resumed with result `result` and exception `error`.

		Scheduled functions do not increase the call stack and might be executed in a different
		thread if the current dispatcher allows that.
	**/
	static public inline function resumeAsync<T>(cont:IContinuation<T>, result:T, error:Exception) {
		cont.context.get(Scheduler).scheduleFunction(() -> cont.resume(result, error));
	}

	/**
	 * Schedules a function to be executed as soon as possible
	 * @param scheduler Scheduler to execute the function on.
	 * @param func Function to execute.
	 * @return Handle which provides a best effort way to cancel the execution of the scheduled function.
	 */
	public static extern inline overload function scheduleFunction(scheduler : Scheduler, func : ()->Void) : ISchedulerHandle {
		return scheduler.schedule(0, null, (_, _) -> {
			func();
		});
	}

	/**
	 * Schedules a function to be executed as soon as possible
	 * @param scheduler Scheduler to execute the function on.
	 * @param state Object to be passed into the function when executed.
	 * @param func Function to execute.
	 * @return Handle which provides a best effort way to cancel the execution of the scheduled function.
	 */
	public static extern inline overload function scheduleFunction<T>(scheduler : Scheduler, state : T, func : (state : T)->Void) : ISchedulerHandle {
		return scheduler.schedule(0, state, (_, s) -> {
			func(s);
		});
	}

	/**
	 * Schedules a function to be executed as soon as possible
	 * @param scheduler Scheduler to execute the function on.
	 * @param state Object to be passed into the function when executed.
	 * @param func Function to execute.
	 * @return Handle which provides a best effort way to cancel the execution of the scheduled function.
	 */
	public static extern inline overload function scheduleFunction<T>(scheduler : Scheduler, state : T, func : (scheduler : Scheduler, state : T)->Void) : ISchedulerHandle {
		return scheduler.schedule(0, state, func);
	}

	/**
	 * Schedules a function to be executed after the specified time has passed.
	 * @param scheduler Scheduler to execute the function on.
	 * @param ms The relative time in milliseconds after which to execute the function.
	 * @param func Function to execute.
	 * @return Handle which provides a best effort way to cancel the execution of the scheduled function.
	 */
	public static extern inline overload function scheduleFunction(scheduler : Scheduler, ms : Int64, func : ()->Void) : ISchedulerHandle {
		return scheduler.schedule(ms, null, (_, _) -> {
			func();
		});
	}

	/**
	 * Schedules a function to be executed after the specified time has passed.
	 * @param scheduler Scheduler to execute the function on.
	 * @param ms The relative time in milliseconds after which to execute the function.
	 * @param state Object to be passed into the function when executed.
	 * @param func Function to execute.
	 * @return Handle which provides a best effort way to cancel the execution of the scheduled function.
	 */
	public static extern inline overload function scheduleFunction<T>(scheduler : Scheduler, ms : Int64, state : T, func : (state : T)->Void) : ISchedulerHandle {
		return scheduler.schedule(ms, state, (_, s) -> {
			func(s);
		});
	}

	/**
	 * Schedules a function to be executed after the specified time has passed.
	 * @param scheduler Scheduler to execute the function on.
	 * @param ms The relative time in milliseconds after which to execute the function.
	 * @param state Object to be passed into the function when executed.
	 * @param func Function to execute.
	 * @return Handle which provides a best effort way to cancel the execution of the scheduled function.
	 */
	public static extern inline overload function scheduleFunction<T>(scheduler : Scheduler, ms : Int64, state : T, func : (scheduler : Scheduler, state : T)->Void) : ISchedulerHandle {
		return scheduler.schedule(ms, state, func);
	}
}