package Expressions;
public class Branching extends Object {
	static int  c;
	ExpressionGen g;
	public static synchronized void add() 
		{
			if(true)
			{
				int  i = c + 5;
				i = 7;
				System.out.println(i);
				c++;
				add();
			}
			if(false)
			{
				int  i = 8;
			}
		}
	public void sub(ExpressionGen p) 
		{
			synchronized(Expressions.Branching.class)
				{
					add();
				}
		}

}