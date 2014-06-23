module refactoring::introducing_shared_state::ConvertLocalToField

import IO;
import String;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::microrefactorings::GetInfo;
import refactoring::microrefactorings::MicroRefactorings;

Declaration newFieldDeclaration;

set[Declaration] convertLocalToField(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	targetedClassDecl = getClassDeclFromMethod(targetedMethodDecl);
	fieldName = extractVariableNameFromDecl(local);
	newFieldDecl = createNewFieldDeclaration(targetedClassDecl, fieldName);
	lockDecl = createNewFieldDeclaration(targetedClassDecl, "generated_lock_for_"+fieldName);
	return top-down-break visit(asts){
		case c:class(name, exts, impls ,body):{
			if(c@decl == targetedClassDecl){
				body = for(b <- body){
					append(convertLocalToField(b, local, targetedClassDecl, targetedMethodDecl, newFieldDecl, lockDecl));
				}
				body = [Declaration::field(simpleType(simpleName("Object")[@decl=|java+class:///java/lang/Object|][@typ=object()]),[variable("generated_lock_for_"+fieldName, 0, newObject(simpleType(simpleName("Object")[@decl=|java+class:///java/lang/Object|][@typ=object()]),[]))])]
					 + [newFieldDeclaration]
				     + body;
				insert class(name, exts, impls ,body)[@modifiers=c@modifiers][@src = c@src][@decl=c@decl][@typ=c@typ];
			}
			else
				fail;
		}
	}
}

Declaration convertLocalToField(Declaration f:field(t,frags), loc local, loc targetedClassDecl, loc targetedMethodDecl, loc newFieldDecl, loc lockDecl){
	for(fr <- frags){
		if(fr@decl == newFieldDecl)
			throw "Field with name <fieldName> already exists at <f@src>";
		if(fr@decl == lockDecl)
			throw "Field with name generated_lock_for_<fieldName> already exists at <f@src>";
	}
	return f;
}

Declaration convertLocalToField(Declaration m:method(r, n, ps, exs, mb), loc local, loc targetedClassDecl, loc targetedMethodDecl, loc newfieldPath, loc lockDecl){
	if(m@decl == targetedMethodDecl){
		locking = simpleName(extractVariableNameFromDecl(lockDecl))[@decl = lockDecl][@typ = object()];
		<mb, newFieldDeclaration> = addInASynchronizedBlock(mb, local, locking);
		return method(r, n, ps, exs, mb)[@src = m@src][@decl = m@decl][@typ = m@typ][@modifiers = m@modifiers];
	}
	else
		return m;
}

default Declaration convertLocalToField(Declaration d, loc local, loc targetedClassDecl, loc targetedMethodDecl, loc newfieldPath, loc lockDecl)
	= d;