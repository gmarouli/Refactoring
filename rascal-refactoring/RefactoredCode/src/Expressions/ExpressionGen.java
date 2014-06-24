package Expressions;
public class ExpressionGen {
	public int  i;
	Branching b;
	public void add(Expressions.Branching param_param) 
		{
			synchronized(param_param)
				{
					if(true)
					{
						int  i = param_param.c + 5;
						i = 7;
						System.out.println(i);
						param_param.c++;
						param_param.g.add(param_param);
					}
					if(false)
					{
						int  i = 8;
						param_param.g.b.g.i++;
						param_param.g.i--;
					}
				}
		}

}