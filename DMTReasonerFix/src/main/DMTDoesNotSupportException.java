package main;
/**
 * An exception we throw when we encounter an operation that we don't support.
 * @author Matt
 *
 */
public class DMTDoesNotSupportException extends RuntimeException {
	
	public DMTDoesNotSupportException(String message) {
		super(message);
	}
	
}
