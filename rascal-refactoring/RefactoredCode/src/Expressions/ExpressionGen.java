package Expressions;
public class ExpressionGen {
	public int  i;
	Branching b;
	public static void add() 
		{
			synchronized(Expressions.Branching.class)
				{
					if(true)
					{
						int  i = c + 5;
						i = 7;
						System.out.println(i);
						c++;
						Expressions.ExpressionGen.add();
					}
					if(false)
					{
						int  i = 8;
					}
				}
		}

}