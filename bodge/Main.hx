import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;

function main() {
    Coroutine.runScoped(scope -> {
        scope.start(_ -> {
            delay(500);

            trace('Hello, ');
        });

        scope.start(_ -> {
            delay(1000);

            trace('World!');
        });

        trace('tasks launched!');
    });
}