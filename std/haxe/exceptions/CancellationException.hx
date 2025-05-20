package haxe.exceptions;

class CancellationException extends Exception {
	public function new() {
		super('Cancellation exception');
	}
}