package Expressions;
public class ExpressionGen {
	public int  i;
	Branching b;
	public void add(Expressions.Branching l) 
		{
			if(true)
			{
				int  i = l.c + 5;
				i = 7;
				System.out.println(i);
				l.c++;
				this.add(l);
			}
			if(false)
			{
				int  i = 8;
				this.b.g.i++;
				l.g.i--;
			}
		}

}