package Expressions;
public class ExpressionGen {
	boolean  a = false;
	volatile boolean  b = false;
	public void m1() 
		{
						int  c = 0;
;
						boolean  x = (c++ == 0);
;
			while(!b);			if(x)
;			System.out.println(c);
		}
	public static void main(String[]  args) 
		{
						ExpressionGen e = new ExpressionGen();
;
			e.m1();
		}

}