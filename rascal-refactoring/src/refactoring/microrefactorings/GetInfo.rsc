module refactoring::microrefactorings::GetInfo

import lang::sccfg::ast::DataFlowLanguage;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import String;
import List;
import IO;

anno loc Declaration @ origDecl;
public set[loc] convertedToPublic = {};

bool isArrayAccess(Expression a:arrayAccess(_,_)) = true;
default bool isArrayAccess(Expression lhs) = false;

public set[loc] getSynchronizedMethods(Program p, rel[loc,loc] callGraph){
	set[loc] synchronizedMethods = {d | acquireLock(_, _, dep) <- p.statements, exitPoint(id, d) <- p.statements, dep == id}
						+ {d | releaseLock(_, _, dep) <- p.statements, entryPoint(id, d) <- p.statements, dep == id};
	iprintln(callGraph);
	newSynchronizedMethods = synchronizedMethods;
	do{
		synchronizedMethods = newSynchronizedMethods;
		newSynchronizedMethods = synchronizedMethods + {decl | <decl, syncDecl> <- callGraph, (syncDecl in synchronizedMethods)};
	}while(synchronizedMethods != newSynchronizedMethods);
	return synchronizedMethods;
}

rel[loc,loc] getCallGraph(set[Declaration] asts){
	rel[loc,loc] invocation = {};
	visit(asts){
		case m:method(_,_,_,_,body):{
			invocation += getMethodCalls(body, m@decl, invocation);
		}
	}
	return invocation;
}

rel[loc, loc] getMethodCalls(Statement body, loc m, rel[loc, loc] invocation){
	visit(body){
		case c:methodCall(_, _, _):{
			invocation += {<m,c@decl>};
		}
		case c:methodCall(_,_, _, _):{
			invocation += {<m,c@decl>};
		}
	}
	return invocation;
}

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
		case e:methodCall(_,_,_):{
			replacementVariables += {e@decl};
		}
		case e:methodCall(_,_,_,_):{
			replacementVariables += {e@decl};
		}
	}
	return replacementVariables;
}

bool isInfix(Expression e:infix(_,_,_,_)) = true;
default bool isInfix(Expression e) = false;

bool isLocalAssignment(Expression e:assignment(lhs,_,_), loc local)
	= !isArrayAccess(lhs) && lhs@decl == local;
bool isLocalAssignment(Expression e:postfix(operand, _), loc local)
	= !isArrayAccess(operand) && operand@decl == local;
bool isLocalAssignment(Expression e:prefix(_, operand), loc local)
	= !isArrayAccess(operand) && operand@decl == local;
default bool isLocalAssignment(Expression e, loc local)
	= false;

bool containsFieldsOrMethods(set[loc] variables){
	for(v <- variables){
		if(v.scheme == "java+field")
			return true;
		if(v.scheme == "java+method")
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
	loc classDecl = getClassDeclFromMethod(method@decl);
	if(static() in (method@modifiers ? {})){
		Expression l = createQualifiedClass(classDecl, method@src);
		return Expression::\type(simpleType(l))[@src = method@src]
											   [@typ = TypeSymbol::class(|java+class:///java/lang/Class|, [l@typ])];
	}
	else{
		return Expression::this()[@src = method@src][@typ = TypeSymbol::class(|java+class:///|+className,[])];
	}
}

Expression createQualifiedClass(loc decl, loc src)
	= simpleName(substring(decl.path,findLast(decl.path,"/")))[@decl = decl][@src = src][@typ = createType(decl)];
	
TypeSymbol createType(loc decl){
	if(decl.scheme == "java+class")
		return class(decl,[]);
	else if(decl.scheme == "java+interface")
		return symbol(decl,[]);
	assert "Unknown type <decl.scheme>";
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
			newMethodDecl.path = substring(newMethodDecl.path,0,findLast(newMethodDecl.path,")")) + replaceAll(substring(from.path,1), "/", ".") +")";
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

bool isField(Expression f:simpleName(_)) = (f@decl.scheme == "java+field");
bool isField(Expression q:qualifiedName(exp, _)) = isField(exp);
default bool isField(Expression exp){
	assert false : "What am I? <exp>";
}

loc getFirstAccessDecl(Expression f:simpleName(name)) 
	= f@decl;
loc getFirstAccessDecl(Expression q:qualifiedName(exp, _))
	= getFirstAccessDecl(exp);
Expression getInitFromVariable(Expression v:variable(_,_)) = Expression::null();
Expression getInitFromVariable(Expression v:variable(_,_, init)) = init;

bool isMethod(Declaration::method(_,_,_,_,_)) = true;
bool isMethod(Declaration::method(_,_,_,_)) = true;
default bool isMethod(Declaration e) = false;
