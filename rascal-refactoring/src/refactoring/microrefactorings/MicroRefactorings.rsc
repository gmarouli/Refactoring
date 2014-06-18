module refactoring::microrefactorings::MicroRefactorings

import refactoring::microrefactorings::GetInfo;
import lang::java::jdt::m3::AST;

Declaration desugarSynchronizedMethod(Declaration targetMethod:method(r, n, p, exc, impl)){
	if(synchronized() in  (targetMethod@modifiers ? {})){
		return method(r, n, p, exc, encloseInSynchronized(targetMethod))[@modifiers = (targetMethod@modifiers - \synchronized())][@src = targetMethod@src][@decl = targetMethod@decl][@typ = targetMethod@typ];
	}
	else{
		return targetMethod;
	}
		
}
	
Declaration sugarSynchronizedMethod(Declaration m:method(r, n, p, exc, impl)){
	switch(impl){
		case s:synchronizedStatement(l,body):{
			if(static() in (method@modifiers ? {}))
				return m;
			else
				return method(r, n, p, exc, body)[@modifiers = (m@modifiers + /synchronized())][@src = m@src][@decl = m@decl][@origDecl = m@origDecl][@typ = m@typ];
		}
		default:{
			return m;
		}	
	}
}

Declaration adaptMethodCall(loc targetMethod, loc sourceClass, loc destinationClass, Statement m:methodCall(isSuper, name, args)){
	return m;
}

Declaration adaptMethodCall(loc targetMethod, loc sourceClass, loc destinationClass, Statement m:methodCall(isSuper, rcv, name, args)){
	return m;
}