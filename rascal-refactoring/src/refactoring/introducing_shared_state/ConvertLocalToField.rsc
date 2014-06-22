module refactoring::introducing_shared_state::ConvertLocalToField

import IO;
import String;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::microrefactorings::GetInfo;
import refactoring::microrefactorings::MicroRefactorings;

set[Declaration] convertLocalToField(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	targetedClassDecl = |java+class:///|+substring(targetedMethodDecl.path,0,findLast(targetedMethodDecl.path,"/"));
	fieldPath = |java+field:///|+substring(targetedMethodDecl.path,0,findLast(targetedMethodDecl.path,"/")+1);
	fieldName = substring(local.path,findLast(local.path,"/")+1);
	lockDecl = fieldPath + "generated_lock_for_"+fieldName;
	Declaration newFieldVariable;
	return top-down-break visit(asts){
		case c:class(name, exts, impls ,body):{
			if(c@decl == targetedClassDecl){
				println(c);
				body = for(b <- body){
					switch(b){
						case f:field(t,frags):{
							frags = for(fr <- frags){
								if(fr@decl == fieldPath + fieldName)
									throw "Field with name <fieldName> already exists at <f@src>";
								if(fr@decl == lockDecl)
									throw "Field with name generated_lock_for_<fieldName> already exists at <f@src>";
								append(fr);
							}
							append(Declaration::field(t,frags)[@src = f@src]);
						}
						case m:method(r, n, ps, exs, mb):{
							if(m@decl == targetedMethodDecl){
								locking = simpleName("generated_lock_for_"+fieldName)[@decl = fieldPath + "generated_lock_for_"+fieldName][@typ = object()];
								<mb, newFieldVariable> = addInASynchronizedBlock(mb, local, locking);
								append(method(r, n, ps, exs, mb)[@src = m@src][@decl = m@decl][@typ = m@typ][@modifiers = m@modifiers]);
							}
							else
								append(m);
						}
						default:
							append(b);
					}
				}
				body += 
				[Declaration::field(simpleType(simpleName("Object")[@decl=|java+class:///java/lang/Object|][@typ=object()]),[variable("generated_lock_for_"+fieldName, 0, newObject(simpleType(simpleName("Object")[@decl=|java+class:///java/lang/Object|][@typ=object()]),[]))])] + 
				[newFieldVariable];
				insert class(name, exts, impls ,body)[@modifiers=c@modifiers][@src = c@src][@decl=c@decl][@typ=c@typ];
			}
			else
				fail;
		}
	}
}
