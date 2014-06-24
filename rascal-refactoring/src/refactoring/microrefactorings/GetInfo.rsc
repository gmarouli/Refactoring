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


bool isTargetMethod(Declaration d, loc targetMethod){
	if(isMethod(d))
		return d@decl != targetMethod; 
	else 
		return true;
}
set[loc] collectVariables(Expression exp, set[loc] replacementVariables){
	visit(exp){
		case e:simpleName(_):{
			replacementVariables += {e@decl};
		}
	}
	return replacementVariables;
}

bool isInfix(Expression e:infix(_,_,_,_)) = true;
default bool isInfix(Expression e) = false;

bool isLocalAssignment(Expression e:assignment(lhs,_,_), loc local)
	= lhs@decl == local;
default bool isLocalAssignment(Expression e, loc local)
	= false;

bool containsFields(set[loc] variables){
	for(v <- variables){
		if(v.scheme == "java+field")
			return true;
	}
	return false;
}
loc getMethodDeclFromVariable(loc variable) 
	= |java+method:///| + substring(variable.path,0,findFirst(variable.path,")")+1);

loc getClassDeclFromMethod(loc method) 
	= |java+class:///|+extractClassName(method);

loc createNewFieldDeclaration(loc class, str name)
	= |java+field:///|+ class.path + "/" + name;

str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));

str extractVariableNameFromDecl(loc variable)
	= substring(variable.path,findLast(variable.path,"/")+1);
	
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
	= block([synchronizedStatement(determineLock(method),impl)[@src = method@src]])[@src = method@src];
	
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
	newMethodDecl = |java+method:///| + to.path + substring(m@decl.path,findLast(m@decl.path,"/"));
	
	if(staticM){
		return newMethodDecl;
	}
	else if(paramM){
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
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + ","+ replaceAll(substring(from.path,1), "/", ".") +")";
		}
		else{
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + ","+ replaceAll(substring(from.path,1), "/", ".") +")";
		}
	}
	return newMethodDecl;
}

bool isFieldOf(Expression f:simpleName(_), loc c) = (f@decl.scheme == "java+field" && substring(f@decl.path,0,findLast(f@decl.path,"/")) == c.path);
bool isFieldOf(Expression q:qualifiedName(exp, _), loc c) = isFieldOf(exp, c);
default bool isFieldOf(Expression exp, c){
	assert false : "What am I? <exp>";
}

loc getFirstAccessDecl(Expression f:simpleName(name)) 
	= f@decl;
loc getFirstAccessDecl(Expression q:qualifiedName(exp, _))
	= getFirstAccessDecl(exp);
Expression getInitFromVariable(Expression v:variable(_,_)) = Expression::null();
Expression getInitFromVariable(Expression v:variable(_,_, init)) = init;

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

bool isMethod(Declaration::method(_,_,_,_,_)) = true;
bool isMethod(Declaration::method(_,_,_,_)) = true;
default bool isMethod(Declaration e) = false;
