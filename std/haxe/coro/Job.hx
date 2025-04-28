package haxe.coro;

class Job {
    final parent : Null<Job>;

    final children : Array<Job>;

    public var completed (get, never) : Bool;

    function get_completed() {
        return false;
    }

    public function new(parent) {
        this.parent = parent;
        
        children = [];
    }

    @:coroutine public function wait() {
        //
    }
}