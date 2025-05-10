package haxe.coro;

import haxe.exceptions.NotImplementedException;

class Job {
    final parent : Null<Job>;

    final children : Array<Job>;

    final completionCallbacks : Array<()->Void>;

    var finished : Bool;

    var completedChildren : Int;

    public var completed (get, never) : Bool;

    function get_completed() {
        return finished && completedChildren == children.length;
    }

    public function new(parent, callback) {
        this.parent = parent;
        
        finished            = false;
        children            = [];
        completionCallbacks = [ callback ];
        completedChildren   = 0;
    }

    public function create() {
        final child = new Job(this, onChildCompleted);

        children.push(child);

        return child;
    }

    public function complete<T>(v:T) {
        finished = true;

        if (completed) {
            for (callback in completionCallbacks) {
                callback();
            }
        }
    }

    public function completeExceptionally(exn:Exception) {
        finished = true;

        throw new NotImplementedException();
    }

    @:coroutine public function await() {
        Coroutine.suspend(cont -> {
            if (completed) {
                cont.resume(null, null);
            } else {
                completionCallbacks.push(() -> cont.resume(null, null));
            }
        });
    }

    function onChildCompleted() {
        completedChildren++;

        if (completed) {
            for (callback in completionCallbacks) {
                callback();
            }
        }
    }
}