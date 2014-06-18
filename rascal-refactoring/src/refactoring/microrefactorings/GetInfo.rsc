module refactoring::microrefactorings::GetInfo

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import String;
import List;
import IO;

anno loc Declaration @ origDecl;

loc newMethodDecl;

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

loc getNewMethodDeclaration(loc from, loc to, Declaration m:method(_,_,ps,_,_), staticM, paramM){
	newMethodDecl = |java+method:///|;
	
	if(staticM){
		newMethodDecl.path = to.path + substring(m@decl.path,findLast(m@decl.path,"/"));
		return newMethodDecl;
	}
	else if(paramM){
		newMethodDecl.path = to.path + substring(m@decl.path,findLast(m@decl.path,"/"));
		newMethodDecl.path = replaceFirst(newMethodDecl.path,replaceAll(substring(to.path,1), "/", "."),"");
		newMethodDecl.path = replaceAll(newMethodDecl.path,",,",",");
		newMethodDecl.path = replaceAll(newMethodDecl.path,",)",")");
		newMethodDecl.path = replaceAll(newMethodDecl.path,"(,","(");
		if(size(ps) == 1)
			newMethodDecl.path = replaceLast(newMethodDecl.path,")",replaceAll(substring(from.path,1), "/", ".")+")");
		else
			newMethodDecl.path = replaceLast(newMethodDecl.path,")",","+replaceAll(substring(from.path,1), "/", ".")+")");
		return newMethodDecl;
	}
	else{
		if(ps == []){
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + replaceAll(substring(from.path,1), "/", ".") +")";
		}
		else{
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + ","+ replaceAll(substring(from.path,1), "/", ".") +")";
		}
	}
	return newMethodDecl;
}

tuple[bool, Declaration] isMethodTransferable(Declaration from:class(_,_,_,bodyFrom), Declaration to:class(_,_,_,bodyTo), Declaration target:method(r, n, ps, exc, body)){
	bool transferable = false;
	Declaration refactoredMethod;
	//check if static
	if(static() in (target@modifiers ? {})){
		println("The method is static! Move on ;)");
		transferable = true;
		newMethodDecl = getNewMethodDeclaration(from@decl, to@decl,target,true,false);
		target = desugarSynchronizedMethod(target);
		body = addQualifiedName(body,from@decl, target@decl);
		refactoredMethod = method(r, n, ps, exc, body)[@modifiers = target@modifiers]
													  [@src = target@src]
													  [@decl = newMethodDecl]
													  [@origDecl = target@decl];
	}
	//if not
	else{
		if(synchronized() in (target@modifiers ? {})){
			println("The method is synchronized but not static! Sorry :(");
			return <false, refactored>;
		}
		//check if the destination class is a parameter 
		ps = visit(ps){
				case p:parameter(simpleType(exp),pname,extr):{
					if(!transferable){
						if(exp@decl == to@decl){
							println("The destination class is a parameter!");
							transferable = true;
							newMethodDecl = getNewMethodDeclaration(from@decl, to@decl,target,false,true);
							insert parameter(simpleType(simpleName(replaceAll(substring(from@decl.path,1), "/", "."))[@src = exp@src][@decl = from@decl][@typ = from@typ]),pname,extr)
									[@src = p@src][@decl = |java+parameter:///|+newMethodDecl.path+"/"+pname][@typ = from@typ];
					}
				}
			}
		}
		//or a field
		if(!transferable){
			for(/f:field(t, _) <- bodyFrom){
				switch(t){
					case simpleType(exp):{
						if(exp@decl == to@decl){
							println("The destination class is a field!");
							transferable = true;
							newMethodDecl = getNewMethodDeclaration(from@decl, to@decl,target, false, false);
							ps = ps + [parameter(simpleType(simpleName(replaceAll(substring(from@decl.path,1), "/", "."))[@src = s@src][@decl = from@decl][@typ = from@typ]),"refactoring_param",extr)
									[@src = p@src][@decl = |java+parameter:///|+newMethodDecl.path+"/"+pname][@typ = from@typ]];
						}
					}
				}
			}
		}
	}
	//check if the destination class contains another method with the same signature
	if(transferable){
		for (/m:method(_,_,_,_,_) <- bodyTo){
			if(m@decl == newMethodDecl){
				println("These is already a method with declaration <newMethodDecl> at <m@src>!");
				return <false,refactored>;
			}
		}
		for (/m:method(_,_,_,_) <- bodyTo){
			if(m@decl == newMethodDecl){
				println("These is already an abstract method with declaration <newMethodDecl> at <m@src>!");
				return <false,refactored>;
			}
		}
	}
	body = addQualifiedName(body,from@decl, target@decl);
	refactoredMethod = method(r, n, ps, exc, body)[@modifiers = target@modifiers]
									  [@src = target@src]
									  [@decl = newMethodDecl]
									  [@origDecl = target@decl];
										//[@typ = target@typ] missing type
	return <true,refactoredMethod>;
}


//Statement accessFieldsThroughParameter(str pname, ){
//}

bool isFieldOf(Expression f, loc c) = (f@decl.scheme == "java+field" && substring(f@decl.path,0,findLast(f@decl.path,"/")) == c.path);

Statement addQualifiedName(Statement b, loc from, loc targetMethod){
	Expression qName = simpleName(replaceAll(substring(from.path,1), "/", "."))
						[@decl=from]
                        [@typ=class(from,[])];
                        
    return top-down-break visit(b){
    	case m:methodCall(isSuper, name, args):{
    		if(m@decl != targetMethod)
	    		insert methodCall(isSuper, qName[@src = m@src], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ];
    	}
    	case s:simpleName(name):{
    		if(isFieldOf(s,from)){
    			insert qualifiedName(qName[@src = s@src], s)[@src = s@src][@decl = s@decl][@typ = s@typ];
    		}
    	}
    	case q:qualifiedName(_,_) => q
    }
}