package Expressions;
import java.io.IOException;
public class Branching extends ExpressionGen {

	void m(int l) {
		;
		try {
			if(l > 0) {
				throw new NullPointerException();
			}
			;
			throw new IOException();
		}
		catch(NullPointerException e) {
			System.out.println(0);
		}
		catch(IOException e) {
			System.out.println(1);
		}
		finally {
			;
			System.out.println(2);
		}
	}

}