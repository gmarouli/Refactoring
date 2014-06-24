package Expressions;
public class Branching extends Object {
	static int  c;
	ExpressionGen g;
	public void add(Expressions.Branching l) 
		{
			if(true)
			{
				int  i = l.c + 5;
				i = 7;
				System.out.println(i);
				l.c++;
				l.add(this);
			}
			if(false)
			{
				int  i = 8;
			}
		}

}