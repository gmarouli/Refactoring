module refactoring::microrefactorings::GetInfo

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import String;
import IO;

str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
Expression determineLock(Declaration method){
	str className = extractClassName(method@decl);
	if(static() in (method@modifiers ? {})){
		return Expression::\type(
								simpleType(
									simpleName(className)
										[@src = method@src]
										[@decl = |java+class:///|+className]
										[@typ = TypeSymbol::class(|java+class:///|+className,[])]
								)
							)[@src = method@src]
							 [@typ = TypeSymbol::class(|java+class:///java/lang/Class|, [TypeSymbol::class(|java+class:///|+className,[])])];
	}
	else{
		return Expression::this()[@src = method@src][@typ = TypeSymbol::class(|java+class:///|+className,[])];
	}
}

Statement encloseInSynchronized(Declaration method:method(_,_,_,_,impl))
	= synchronizedStatement(determineLock(method),impl)[@src = method@src];
	
Declaration getMethodFromSrc(set[Declaration] asts, loc src){
	for (/m:method(_,_,_,_,_) <- asts){
		if(m@src == src){
			return m;
		}
	}
	throw "These is no method at location <src>!";
}

Declaration getClassFromDecl(set[Declaration] asts, loc decl){
	for (/c:class(_,_,_,_) <- asts){
		if(c@decl == decl){
			return c;
		}
	}
	for (/c:class(_) <- asts){
		if(c@decl == decl){
			return c;
		}
	}
	throw "These is no class with that declaration <decl>!";
}