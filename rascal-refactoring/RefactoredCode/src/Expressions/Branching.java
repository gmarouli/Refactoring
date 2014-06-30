package Expressions;
public class Branching {
	private Object generated_lock_for_x = new Object();
	private int  x;
	public void m(int  caller) 
		{
			synchronized(generated_lock_for_x)
				{
					x = 0;
					for(int  i = 0; i < 100000; i++);					x++;
					System.out.println(caller + "": I am exiting with x ="" + x);
				}
		}
	public void m1() 
		{
			m(1);
		}
	public void m2() 
		{
			m(2);
		}

}