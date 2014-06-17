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
	
Declaration getMethodFromDecl(set[Declaration] asts, loc decl){
	for (/m:method(_,_,_,_,_) <- asts){
		if(m@decl == decl){
			return m;
		}
	}
	throw "These is no method with declaration <decl>!";
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

loc getNewMethodDeclaration(loc from, loc to, Declaration m:method(_,_,ps,_,_)){
	loc newMethodDecl = |java+method:///|;
	newMethodDecl.path = to.path + substring(m@decl.path,findLast(m@decl.path,"/"));
	//if the method is not static then we need to add one more parameter in the declaration
	if(!(static() in (m@modifiers ? {}))){
		if(ps == []){
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + replaceAll(substring(from.path,1), "/", ".") +")";
		}
		else{
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + ","+ replaceAll(substring(from.path,1), "/", ".") +")";
		}
	}
	return newMethodDecl;
}

bool isMethodTransferable(Declaration from:class(_,_,_,bodyFrom), Declaration to:class(_,_,_,bodyTo), Declaration target:method(_, _, ps, _, _)){
	loc newMethodDecl = getNewMethodDeclaration(from@decl, to@decl,target);
	//check if the destination class contains another method with the same signature
	for (/m:method(_,_,_,_,_) <- bodyTo){
		if(m@decl == newMethodDecl){
			println("These is already a method with declaration <newMethodDecl> at <m@src>!");
			return false;
		}
	}
	for (/m:method(_,_,_,_) <- bodyTo){
		if(m@decl == newMethodDecl){
			println("These is already an abstract method with declaration <newMethodDecl> at <m@src>!");
			return false;
		}
	}
	//check if static
	if(static() in (target@modifiers ? {})){
		println("The method is static! Move on ;)");
		return true;
	}
	//if not
	else{
		if(synchronized() in (target@modifiers ? {})){
			println("The method is synchronized but not static! Sorry :(");
			return false;
		}
		//check if the destination class is a parameter 
		for(p:parameter(t, _, _) <- ps){
			switch(t){
				case simpleType(exp):{
					if(exp@decl == to@decl){
						println("The destination class is a parameter <p>!");
						return true;
					}
				}
			}
		}
		//or a field
		for(/f:field(t, _) <- bodyFrom){
			switch(t){
				case simpleType(exp):{
					if(exp@decl == to@decl){
						println("The destination class is a field <f>!");
						return true;
					}
				}
			}
		}
	}
	return false;
}