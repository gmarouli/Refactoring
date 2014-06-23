package Expressions;
 class Branching extends Object {
	Object generated_lock_for_i = new Object();
	int  i;
	int  c;
	void add() 
		{
			if(true)
			{
				synchronized(generated_lock_for_i)
					{
						i = c + 5;
						i = 7;
						System.out.name(i);
					}
				c++;
			}
			if(false)
			{
				int  i = 8;
			}
		}

}