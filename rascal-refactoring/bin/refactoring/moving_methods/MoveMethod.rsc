module refactoring::moving_methods::MoveMethod

import IO;
import List;
import String;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::microrefactorings::GetInfo;
import refactoring::moving_methods::StaticMethodCase;
import refactoring::moving_methods::TargetClassInFieldCase;
import refactoring::moving_methods::TargetClassInParameterCase;



public loc unlocked = |lock:///|;

Declaration addMethod(Declaration targetClass:class(name, ext, impl, body), Declaration target){
	return class(name, ext, impl, body+[target])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
	
}

bool isMethod(Declaration::method(_,_,_,_,_)) = true;
bool isMethod(Declaration::method(_,_,_,_)) = true;
default bool isMethod(Declaration e) = false;

data MethodCase = \static(loc decl, Expression receiver)
			| inParameters(loc decl, int index)
			| inFields(loc decl, Expression fieldExp, Declaration param)
			| notTransferable(); 
			
Declaration removeMethod(Declaration targetClass:class(name, ext, impl, body), loc targetMethod){
	return class(name, ext, impl, [d | d <- body, isTargetMethod(d, targetMethod)])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
}

bool isTargetMethod(Declaration d, loc targetMethod){
	if(isMethod(d))
		return d@decl != targetMethod; 
	else 
		return true;
}

set[Declaration] moveMethod(set[Declaration] asts, loc methodDecl, loc destinationClassDecl){
	Declaration targetMethod = getMethodFromDecl(asts, methodDecl);
	Declaration sourceClass = getClassFromDecl(asts, |java+class:///|+extractClassName(targetMethod@decl));
	Declaration destinationClass = getClassFromDecl(asts, destinationClassDecl);
	
	methodConfig = getMovedMethodConfiguration(sourceClass, destinationClass, targetMethod);
	
	if(methodConfig :=  notTransferable()){
		println("The refactoring cannot be applied to <methodDecl>");
		return ast;
	}
	targetMethod = adaptMethodsCode(methodConfig, targetMethod);
	
	asts = top-down-break visit(asts){
		case c:class(name, exts, impls, body):{
			if(c@decl == sourceClass@decl){
				insert removeMethod(c, methodDecl);
			}
			else if(c@decl == destinationClass@decl)
				insert addMethod(c, targetMethod);
			else
				fail;
		}
	}
	return visit(asts){
		case m:methodCall(_, _, _, _):{
			if(m@decl == methodDecl)
				insert adaptMethodCall(methodConfig, m);
			else
				fail;
		}
		case m:methodCall(_, _, _):{
			if(m@decl == methodDecl)
				insert adaptMethodCall(methodConfig, m);
			else
				fail;
		} 
	}
}

Declaration adaptMethodsCode(MethodCase s:inFields(decl, fieldExp, param), Declaration m:method(r, name, list[Declaration] ps, exs, body)){
	oldDecl = m@decl;
	paramDecl = param@decl;
	from = getClassDeclFromMethod(m@decl);
	newParam = simpleName(extractVariableNameFromDecl(param@decl))[@decl = param@decl][@typ = class(from,[])];	
	body = adaptCallsAndFields(body, decl, m@decl, from, fieldExp, newParam);
	return method(r, name, ps + [param[@decl = m@decl]], exs, body)[@decl = decl][@modifiers = m@modifiers];
}

MethodCase getMovedMethodConfiguration(Declaration from:class(_, _, _, body), Declaration to, Declaration m:method(r, n, ps, exs, b)){
	//find the configuration if the method is static
	if(static() in (m@modifiers ? {})){
		println("The method is static! Move on ;)");
		transferable = true;
		receiver = createQualifiedName(to@decl);
		newDecl = getNewMethodDeclaration(from@decl, to@decl, m, true, false);	
		return MethodCase::\static(newDecl, receiver);
	}
	
	//find the configuration if the target class is a parameter of the method
	for(p:parameter(simpleType(exp),pname,extr) <- ps){
		if(exp@decl == to@decl){
			println("The destination class is a parameter!");
			newDecl = getNewMethodDeclaration(from@decl, to@decl, m, false, true);
			index = indexOf(ps,p);
			return MethodCase::inParameters(newDecl, index);
		}
	}
	
	//find the configuration if the target class is a field of the source class
	pname = "param_param";
	for(/f:field(simpleType(exp), [v,*vs]) <- body){
		if(exp@decl == to@decl){
			println("The destination class is a field!");
			newDecl = getNewMethodDeclaration(from@decl, to@decl, m, false, false);
			fname = extractVariableNameFromDecl(v@decl);
			fieldExp = simpleName(fname)[@decl = v@decl];
			param = Declaration::parameter(simpleType(createQualifiedName(from@decl)[@src = m@src]), pname, 0)[@src = m@src][@decl = |java+parameter:///|+newDecl.path+"/"+pname][@typ = from@typ];
			return MethodCase::inFields(newDecl, fieldExp, param);
		}
	}
	return notTransferable();
}


//Statement adaptMethodCalls(MethodCase s, loc oldDecl, Statement body){
//	return visit(body){
//		case m:methodCall(isSuper, name, args):{
//			if(m@decl == oldDecl){
//				insert adaptMethodCall(s,m);
//			}
//			else
//				fail;
//		}
//		case m:methodCall(isSuper, rec, name, args):{
//			if(m@decl == oldDecl){
//				insert adaptMethodCall(s,m);
//			}
//			else
//				fail;
//		}
//	}
//}

Declaration adaptMethodsCode(MethodCase s:inParameters(loc decl, int index), Declaration m:method(r, name, ps, exs, body)){
	oldDecl = m@decl;
	paramDecl = ps[index]@decl;
	from = getClassDeclFromMethod(m@decl);
	to = getClassDeclFromMethod(decl);
	ps = replaceWithNewParameter(ps, index, from, decl);
	body = renameParameterAndThis(body, paramDecl, ps[index]@decl, from, to);
	body = adaptMethodCalls(s, m@decl, body);
	return method(r, name, ps, exs, body)[@decl = decl][@modifiers = m@modifiers];
}

Expression adaptMethodCall(MethodCase s:inParameters(loc decl, int index), m:methodCall(isSuper, name, args)){
	from = getClassDeclFromMethod(decl);
	rec = args[index];
	if((index+1) < size(args))
		args = args[0..index]+[this()[@decl = from]]+args[index+1..];
	else
		args = args[0..index]+[this()[@decl = from]];
	return methodCall(isSuper, rec, name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

Expression adaptMethodCall(MethodCase s:inParameters(loc decl, int index), Expression m:methodCall(isSuper, rec, name, args)){
	newRec = args[index];
	if((index+1) < size(args))
		args = args[0..index]+[receiver]+args[index+1..];
	else
		args = args[0..index]+[rec];
	return methodCall(isSuper, newRec, name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}


list[Declaration] replaceWithNewParameter(list[Declaration] ps, int index, loc from, loc methodDecl){
	newParam = replaceParameterType(ps[index], from, methodDecl);
	if((index+1) < size(ps))
		ps = ps[0..index]+[newParam]+ps[index+1..];
	else
		ps = ps[0..index]+[newParam];
	return ps;
}

Declaration replaceParameterType(Declaration p:parameter(simpleType(exp), name, d), loc from, loc methodDecl){
	return Declaration::parameter(simpleType(createQualifiedName(from)[@src = exp@src]), name, d)[@src = p@src][@decl = |java+parameter:///|+methodDecl.path+"/"+name][@typ = class(from,[])];
}

Statement renameParameterAndThis(Statement body, loc oldMethodDecl, loc newMethodDecl, loc paramDecl, loc newParamDecl, loc from, loc to){
	newParam = simpleName(extractVariableNameFromDecl(newParamDecl))[@decl = newParamDecl][@typ = class(from,[])];
	//to = getClassDeclFromMethod(decl);
	return top-down-break visit(body){
		case q:qualifiedName(_,_):{
			if(isFieldOf(q, from)){
				insert accessThroughVariable(q, newParam);
			}
			else if(getFirstAccessDecl(q) == paramDecl){
				insert insertAccessThroughThis(q, to);
			}
			else
				insert q;
		}
		case f:fieldAccess(isSuper, exp, name) => convertFieldToQualified(f, newParam)
		case e:this():{
			insert newParam[@src = e@src];
		}
		case e:simpleName(name):{
			if(e@decl == paramDecl){
				insert this()[@decl = paramDecl][@typ = e@typ];
			}
			else if(isFieldOf(e, from)){
				insert qualifiedName(newParam, e)[@src = e@src][@decl = e@decl][@typ = e@typ];
			}
		}
		case m:methodCall(isSuper, name, args):{
			if(m@decl == oldMethodDecl){
				args = for(arg <- args){
					expressionStatement(arg) = renameParameterAndThis(expressionStatement(arg), paramDecl, newParamDecl, from, to);
					append(arg);
				}
				insert methodCall(isSuper, newParam, name, args)[@decl = newMethodDecl][@typ = m@typ][@src = m@src];
			}
			else
				fail;
		}
	}
}

Statement adaptCallsAndFields(Statement body, loc newDecl, loc oldDecl, loc from, Expression fieldExp, Expression newParam){
	return top-down-break visit(body){
		case q:qualifiedName(_,_):{
			if(isFieldOf(q, from)){
				insert accessThroughVariable(q, newParam);
			}
			else
				insert q;
		}
		case f:fieldAccess(_, _, _) => convertFieldToQualified(f, newParam)
		case e:this():{
			insert newParam[@src = e@src];
		}
		case e:simpleName(name):{
			if(isFieldOf(e, from)){
				insert qualifiedName(newParam, e)[@src = e@src][@decl = e@decl][@typ = e@typ];
			}
		}
		case m:methodCall(isSuper, name, list[Expression] args):{
			if(m@decl == oldDecl){
				args = for(arg <- args){
					expressionStatement(arg) = adaptCallsAndFields(expressionStatement(arg), newDecl, oldDecl, from, fieldExp, newParam);
					append(arg);
				}
				args += [newParam];
				//careful not nice src
				insert methodCall(isSuper, qualifiedName(newParam[@src = m@src], fieldExp[@src = m@src]), name, args)[@decl = newDecl][@typ = m@typ][@src = m@src];
			}
			else 
				fail;
		}
		case m:methodCall(isSuper, rec, name, args):{
			if(m@decl == oldDecl){
				args = for(arg <- args){
					expressionStatement(arg) = adaptCallsAndFields(expressionStatement(arg), newDecl, oldDecl, from, fieldExp, newParam);
					append(arg);
				}
				args += [rec];
				//careful not nice src
				insert methodCall(isSuper, qualifiedName(rec, fieldExp[@src = m@src]), name, args)[@decl = newDecl][@typ = m@typ][@src = m@src];
			}
			else
				fail;
		}
	}
}

Expression accessThroughVariable(Expression s:simpleName(_), Expression newParam)
	= qualifiedName(newParam[@src = s@src], s)[@src = s@src][@src = s@src][@typ = s@typ]; 
Expression accessThroughVariable(Expression q:qualifiedName(exp,f), Expression newParam)
	= qualifiedName(accessThroughVariable(exp,newParam), f)[@src = q@src][@decl = q@decl][@typ = q@typ]; 
	
Expression convertFieldToQualified(Expression f:fieldAccess(_, t:this(), name), Expression newParam)
	= qualifiedName(newParam[@src = t@src], simpleName(name)[@decl = f@decl][@src = f@src][@typ = f@typ]);
Expression convertFieldToQualified(Expression f:fieldAccess(_, exp, name), Expression newParam)
	= qualifiedName(convertFieldToQualified(exp, newParam), simpleName(name)[@decl = f@decl][@src = f@src][@typ = f@typ]);
default Expression convertFieldToQualified(Expression f, Expression newParam){
	println(f);
	}

Expression insertAccessThroughThis(Expression q:qualifiedName(simpleName(_), s:simpleName(name)), loc to)
	= fieldAccess(false, \this()[@typ = class(to,[])][@decl = s@decl][@src = s@src],name);
Expression insertAccessThroughThis(Expression q:qualifiedName(exp, s:simpleName(name)), loc to)
	= fieldAccess(false, insertAccessThroughThis(exp, to), name);
	
Expression adaptMethodCall(MethodCase s:inFields(decl, fieldExp, param), Expression m:methodCall(isSuper, name, list[Expression] args)){
	from = getClassDeclFromMethod(decl);
	args += [\this()[@typ = class(from,[])]];
	return methodCall(isSuper, fieldExp[@src = m@src], name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

Expression adaptMethodCall(MethodCase s:inFields(decl, fieldExp, param), Expression m:methodCall(isSuper, rec, name, args)){	
	return methodCall(isSuper, qualifiedName(rec, fieldExp[@src = m@src]), name, args + [rec])[@decl = decl][@typ = m@typ][@src = m@src];
}