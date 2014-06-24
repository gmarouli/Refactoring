package Expressions;
public class Branching extends Object {
	static int  c;
	ExpressionGen g;
	public void sub(ExpressionGen p) 
		{
			synchronized(Expressions.Branching.class)
				{
					Expressions.ExpressionGen.add();
				}
		}

}