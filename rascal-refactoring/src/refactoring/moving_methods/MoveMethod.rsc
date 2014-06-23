module refactoring::moving_methods::MoveMethod

import IO;
import List;
import String;
import lang::java::jdt::m3::AST;
import refactoring::microrefactorings::GetInfo;


public loc unlocked = |lock:///|;

Declaration addMethod(Declaration targetClass:class(name, ext, impl, body), Declaration target){
	return class(name, ext, impl, body+[target])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
	
}

bool isMethod(method(_,_,_,_,_)) = true;
bool isMethod(method(_,_,_,_)) = true;
default bool isMethod(e) = false;

data MethodCase = \static(loc decl, Expression receiver)
			| inParameters(loc decl, int index)
			| inFields(loc decl, Expression field, Declaration param)
			| notTransferable(); 
			
Declaration removeMethod(Declaration targetClass:class(name, ext, impl, body), Declaration targetMethod){
	return class(name, ext, impl, [d | d <- body, isTargetMethod(d, targetMethod@decl)])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
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
	asts = moveMethod(asts, methodConfig, sourceClass@decl, destinationClass@decl, targetMethod@decl);
	return asts;
}

//set[Declaration] moveMethod(set[Declaration] asts, MethodCase config:\static(decl, rec), loc from, loc to, Declaration method){
//	visit(asts){
//		case c:class(_, _, _, b):{
//			if(c@decl == 
//		}
//	}
//}

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

Expression createQualifiedName(loc decl){
	parts = split("/", decl.path);
	parts = [p | p <- parts, p != ""];
	parts = reverse(parts);
	return createQualifiedName(parts, |java+class:///|);
}

Expression createQualifiedName(list[str] s:[x], loc scheme){
	return simpleName(x)[@decl = (scheme + x)];
}

Expression createQualifiedName(list[str] s:[x,*xs], loc scheme){
	path = x;
	for(p <- xs){
		path = p + "/" + path;
	}
	return qualifiedName(createQualifiedName(xs,|java+package:///|), simpleName(x)[@decl = scheme + path])[@decl = scheme + path];
}
