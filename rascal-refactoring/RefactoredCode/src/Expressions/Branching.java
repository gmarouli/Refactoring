package Expressions;
import java.io.IOException;
public class Branching extends ExpressionGen {
	int f;
	ExpressionGen l;

	public int add(Branching b, Branching c)  throws {
		int i = 0;
		int k = 0;
		while(i == 3) {
			if(k == 0) {
				i = 5;
				continue;
			}
			else if(k == 4) {
				i = 6;
				break;
			}
			else if(k == 9) {
				i ++;
			}
			else {
				return i ++;
			}
		}
		return i;
	}

	public int sub()  throws {
		return 0;
	}

}