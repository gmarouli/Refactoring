package Expressions;
public class ExpressionGen {
	private Object generated_lock_for_x = new Object();
	private boolean  x;
	volatile boolean  a = false;
	volatile boolean  b = false;
	public void m1() 
		{
			synchronized(generated_lock_for_x)
				{
					x = (a = true);
					while(!b);					
					if(x);
				}
		}

}