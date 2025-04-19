package haxe.coro.context;

class Key<T> {
    public final id : String;

    public function new(id : String) {
        this.id = id;
    }
}