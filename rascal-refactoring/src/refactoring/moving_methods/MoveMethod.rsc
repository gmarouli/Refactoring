module refactoring::moving_methods::MoveMethod

import IO;
import List;
import String;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::microrefactorings::GetInfo;


public loc unlocked = |lock:///|;

Declaration addMethod(Declaration targetClass:class(name, ext, impl, body), Declaration target){
	return class(name, ext, impl, body+[target])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
	
}

bool isMethod(Declaration::method(_,_,_,_,_)) = true;
bool isMethod(Declaration::method(_,_,_,_)) = true;
default bool isMethod(Declaration e) = false;

data MethodCase = \static(loc decl, Expression receiver)
			| inParameters(loc decl, int index)
			| inFields(loc decl, Expression field, Declaration param)
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
	
	targetMethod = adaptMethod(methodConfig, targetMethod);
	
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
