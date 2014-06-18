module refactoring::moving_methods::MoveMethod

import lang::java::jdt::m3::AST;
import refactoring::microrefactorings::GetInfo;
import IO;

public loc unlocked = |lock:///|;

public Expression receiver;
public bool flip = false;

Declaration addMethod(Declaration targetClass:class(name, ext, impl, body), Declaration target){
	return class(name, ext, impl, body+[target])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
	
}

Declaration removeMethod(Declaration targetClass:class(name, ext, impl, body), Declaration targetMethod){
	return class(name, ext, impl, [d | d <- body, d@decl != targetMethod@decl])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
}

set[Declaration] moveMethod(set[Declaration] asts, loc methodDecl, loc destinationClassDecl){
	Declaration targetMethod = getMethodFromDecl(asts, methodDecl);
	Declaration sourceClass = getClassFromDecl(asts, |java+class:///|+extractClassName(targetMethod@decl));
	Declaration destinationClass = getClassFromDecl(asts, destinationClassDecl);
	<transferable, refactored> = isMethodTransferable(sourceClass, destinationClass, targetMethod);
	if(transferable){
		println("Applying refactoring");
		iprintln(visit(asts){
			case c:class(_,_,_,body):{
				if(c@decl == sourceClass@decl){
					println("Found source class : <sourceClass@decl>");
					insert  removeMethod(sourceClass,targetMethod);
				}
				else if (c@decl == destinationClass@decl){
					println("Found destination class : <destinationClassDecl>");
					insert  addMethod(destinationClass, refactored);
				}
			}
			case m:methodCall(isSuper, name, args) => adaptMethodCall(targetMethod@decl, sourceClass@decl, destinationClass@decl, m)
			case m:methodCall(isSuper, rec, name, args) => adaptMethodCall(targetMethod@decl, sourceClass@decl, destinationClass@decl, m)
		});
	}
	return {};
}



