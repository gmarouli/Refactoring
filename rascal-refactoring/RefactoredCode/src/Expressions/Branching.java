package Expressions;
 class Branching extends Object {
	int  c;
	void add() 
		{
			if(true)
			{
				synchronized(generated_lock_for_i)
					{
						i = c + 5;
						c--;
						System.out.name(i);
					}
				c++;
			}
			if(false)
			{
				int  i = 8;
			}
		}
	Object generated_lock_for_i = new Object();
	int  i;

}