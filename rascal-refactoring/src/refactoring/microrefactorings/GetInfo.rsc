module refactoring::microrefactorings::GetInfo

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import String;
import List;
import IO;

anno loc Declaration @ origDecl;

loc newMethodDecl;
public set[loc] convertedToPublic = {};
public bool swap = false;
public int index = -1;
public bool field = false;
public str fname = "";

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
							swap = true;
							index = indexOf(ps,p);
							transferable = true;
							newMethodDecl = getNewMethodDeclaration(from@decl, to@decl,target,false,true);
							body = accessFieldsThroughParameterSwap(body, pname, from@decl, to@decl,target@decl);
							insert parameter(simpleType(simpleName(replaceAll(substring(from@decl.path,1), "/", "."))[@src = exp@src][@decl = from@decl][@typ = from@typ]),pname,extr)
									[@src = p@src][@decl = |java+parameter:///|+newMethodDecl.path+"/"+pname][@typ = from@typ];
					}
				}
			}
		}
		//or a field
		if(!transferable){
			pname = "param_param";
			for(/f:field(t, _) <- bodyFrom){
				switch(t){
					case simpleType(exp):{
						if(exp@decl == to@decl){
							println("The destination class is a field!");
							transferable = true;
							field = true;
							fname = exp;
							convertedToPublic += {f@decl};
							newMethodDecl = getNewMethodDeclaration(from@decl, to@decl,target, false, false);
							body = accessFieldsThroughParameterSwap(body, pname, from@decl, to@decl,target@decl);
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
    		//make sure that the call does not refer to itself
    		if(m@decl != targetMethod){
    			convertedToPublic += {m@decl};
	    		insert methodCall(isSuper, qName[@src = m@src], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ];
	    	}
	    	else
	    		fail;
    	}
    	case s:simpleName(name):{
    		if(isFieldOf(s,from)){
    			convertedToPublic += {s@decl};
    			insert qualifiedName(qName[@src = s@src], s)[@src = s@src][@decl = s@decl][@typ = s@typ];
    		}
    	}
    	case q:qualifiedName(_,_) => q
    }
}

Statement accessFieldsThroughParameterSwap(Statement b, str pname, loc from, loc to, loc targetMethod){
	Expression p = simpleName(pname)[@decl = |java+parameter:///|+newMethodDecl.path+"/"+pname][@typ=class(from,[])];
	return top-down-break visit(b){
    	case m:methodCall(isSuper, name, args):{
    		//if the method call does not refer to the target method we add the parameter
    		if(m@decl != targetMethod){
    			convertedToPublic += {m@decl};
	    		insert methodCall(isSuper, p[@src = m@src], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ];
			}
			else
				fail;
    	}
    	case m:methodCall(isSuper, \this(), name, args):{
    		//if the method call does not refer to the target method we add the parameter
    		if(m@decl != targetMethod){
    			convertedToPublic += {m@decl};
	    		insert methodCall(isSuper, p[@src = m@src], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ];
	    	}
	    	else
	    		fail;
    	}
    	case m:methodCall(isSuper, simpleName(pname), name, args) =>
    		methodCall(isSuper, this()[@src = s@src][@typ = class(to,[])], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ]
  
    	case s:fieldAccess(isSuper, exp, name):{
    		if(exp == this()){
    			convertedToPublic += {s@decl};
    			insert qualifiedName(p[@src = s@src], simpleName(name)[@src = s@src][@decl = s@decl][@typ = s@typ])[@src = s@src][@decl = s@decl][@typ = s@typ];
    		}
    		else{
    			assert true : "field access, no this";
    			fail;
    		}
    	}
    	case s:qualifiedName(q,e:simpleName(name)) :{
 			if(q@decl == |java+parameter:///|+targetMethod.path+"/"+pname){//needs fixing
    			insert fieldAccess(false, this()[@src = s@src][@typ = class(to,[])], name)[@src = s@src][@decl = e@decl][@typ = e@typ];
    		}
    		else
    			fail;
    	}
    	case s:simpleName(name):{
 			if(name == pname){
    			insert this()[@src = s@src][@typ = class(to,[])];
    		}
    		else if(isFieldOf(s,from)){
    			convertedToPublic += {s@decl};
    			insert qualifiedName(p[@src = s@src], s)[@src = s@src][@decl = s@decl][@typ = s@typ];
    		}
    		else
    			fail;
    	}
    }
}

Statement accessFieldsThroughParameter(Statement b, str pname, loc from, loc to, loc targetMethod){
	Expression p = simpleName(pname)[@decl = |java+parameter:///|+newMethodDecl.path+"/"+pname][@typ=class(from,[])];
	return top-down-break visit(b){
    	case m:methodCall(isSuper, name, args):{
    		//if the method call does not refer to the target method we add the parameter
    		if(m@decl != targetMethod){
    			convertedToPublic += {m@decl};
	    		insert methodCall(isSuper, p[@src = m@src], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ];
			}
			else
				fail;
    	}
    	case m:methodCall(isSuper, \this(), name, args):{
    		//if the method call does not refer to the target method we add the parameter
    		if(m@decl != targetMethod){
    			convertedToPublic += {m@decl};
	    		insert methodCall(isSuper, p[@src = m@src], name, args)[@src = m@src][@decl = m@decl][@typ = m@typ];
	    	}
	    	else
	    		fail;
    	}
    	case s:fieldAccess(isSuper, exp, name):{
    		if(exp == this()){
    			convertedToPublic += {s@decl};
    			insert qualifiedName(p[@src = s@src], simpleName(name)[@src = s@src][@decl = s@decl][@typ = s@typ])[@src = s@src][@decl = s@decl][@typ = s@typ];
    		}
    		else{
    			assert true : "field access, no this";
    			fail;
    		}
    	}
    	case s:qualifiedName(q,e:simpleName(name)) :{
 			if(q@decl == |java+parameter:///|+targetMethod.path+"/"+pname){//needs fixing
    			insert fieldAccess(false, this()[@src = s@src][@typ = class(to,[])], name)[@src = s@src][@decl = e@decl][@typ = e@typ];
    		}
    		else
    			fail;
    	}
    	case s:simpleName(name):{
 			if(name == pname){
    			insert this()[@src = s@src][@typ = class(to,[])];
    		}
    		else if(isFieldOf(s,from)){
    			convertedToPublic += {s@decl};
    			insert qualifiedName(p[@src = s@src], s)[@src = s@src][@decl = s@decl][@typ = s@typ];
    		}
    		else
    			fail;
    	}
    }
}

Expression adaptMethodCall(m:methodCall(isSuper, rec, name, args), loc from, loc to){
	if(swap){
		newArgs = [];
		//missing check if arguement was null
		if((index+1) < size)
			newArgs = args[0..index]+[rec]+args[index+1..];
		else
			newArgs = args[0..index]+[rec];
		return methodCall(isSuper, args[index], name, newArgs)[@decl = newMethodDecl][@src = m@src][@typ = m@typ];
	}
	else if(field){
		return methodCall(isSuper, qualifiedName(rec,simpleName(fname)[@src = rec@src][@decl = to][@typ = class(to,[])]), name, args+[rec]);
	}
}

Expression adaptMethodCall(m:methodCall(isSuper, name, args), loc from, loc to){
	if(swap){
		newArgs = [];
		//missing check if arguement was null
		if((index+1) < size(args))
			newArgs = args[0..index]+[\this()[@src = m@src][@typ = class(from,[])]]+args[index+1..];
		else
			newArgs = args[0..index]+[\this()[@src = m@src][@typ = class(from,[])]];
		return methodCall(isSuper, args[index], name, newArgs)[@decl = newMethodDecl][@src = m@src][@typ = m@typ];
	}
	else if(field){
		return methodCall(isSuper, simpleName(fname)[@src = rec@src][@decl = to][@typ = class(to,[])], name, args+[\this()[@src = m@src]]);
	}
}