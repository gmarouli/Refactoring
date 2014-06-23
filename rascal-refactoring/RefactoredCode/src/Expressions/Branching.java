package Expressions;
public class Branching extends Object {
	static int  c;
	ExpressionGen g;
	void add(Expressions.Branching l) 
		{
			if(true)
			{
				int  i = c + 5;
				i = 7;
				System.out.println(i);
				c++;
				Expressions.ExpressionGen.add(l);
			}
			if(false)
			{
				int  i = 8;
			}
		}

}