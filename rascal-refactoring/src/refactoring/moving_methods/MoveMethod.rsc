module refactoring::moving_methods::MoveMethod

import IO;
import List;
import Set;
import String;

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::util::Getters;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::microrefactorings::GetInfo;
import refactoring::microrefactorings::MicroRefactorings;
import lang::sccfg::converter::Java2SDFG;
import refactoring::rearranging_code::GenerateIds;

data MethodCase = \static(loc decl, Expression receiver)
			| inParameters(loc decl, int index, loc origParam, loc newParam)
			| inFields(loc decl, Expression fieldExp, Declaration param)
			| notTransferable(); 

set[Declaration] moveMethod(set[Declaration] asts, loc methodDecl, loc destinationClassDecl){
	asts = desugarAccessToFields(asts, methodDecl);

	Declaration targetMethod = getMethodFromDecl(asts, methodDecl);
	Declaration sourceClass = getClassFromDecl(asts, |java+class:///|+extractClassName(targetMethod@decl));
	Declaration destinationClass = getClassFromDecl(asts, destinationClassDecl);
	
	methodConfig = getMovedMethodConfiguration(sourceClass, destinationClass, targetMethod);
	
	if(methodConfig :=  notTransferable()){
		println("The refactoring cannot be applied to <methodDecl>");
		return ast;
	}
	
	targetMethod = desugarSynchronizedMethod(targetMethod);
	targetMethod = adaptMethodsCode(methodConfig, targetMethod);
	
	refactoredAsts = top-down-break visit(asts){
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
	refactoredAsts = visit(refactoredAsts){
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
	
	p = createDFG(asts);
	pR = createDFG(refactoredAsts);
		
	if(checkMoveMethod(p,pR, methodDecl, sourceClass@decl, destinationClassDecl, methodConfig)){
		println("Refactoring Move Method successful!");
		return refactoredAsts;
	}
	else{
		println("Refactoring failed!");
		return asts;
	}
}

bool checkMoveMethod(Program p, Program pR, loc methodDecl, loc sourceClassDecl, loc destinationClassDecl, MethodCase config:\static(decl, receiver)){
	differences = p.statements - pR.statements;
	differencesR = pR.statements - p.statements;
	checked = {s1, s2 | s1:entryPoint(id1, methodDecl) 			<- differences, s2:entryPoint(id2, decl) 					<- differencesR, id1 == id2}
			+ {s1, s2 | s1:exitPoint(id1, methodDecl) 			<- differences, s2:exitPoint(id2, decl) 					<- differencesR, id1 == id2}
			+ {s1, s2 | s1:read(id1, sourceClassDecl, dep1) 	<- differences, s2:read(id2, destinationClassDecl, dep2) 	<- differencesR, id1 == id2}
			+ {s1, s2 | s1:change(id1, sourceClassDecl, dep1) 	<- differences, s2:change(id2, destinationClassDecl, dep2) 	<- differencesR, id1 == id2}
			+ {s1, s2 | s1:call(id1, r1, methodDecl, dep1) 		<- differences, s2:call(id2, r2, decl, dep2) 				<- differencesR, id1 == id2, r1 == r2, dep1 == dep2}
			;
	return (differences + differencesR) == checked;
}

bool checkMoveMethod(Program p, Program pR, loc methodDecl, loc sourceClassDecl, loc destinationClassDecl, MethodCase config:inParameters(loc decl, int index, loc origParam, loc newParam)){
	differences = p.statements - pR.statements;
	differencesR = pR.statements - p.statements;
	sourceThis = sourceClassDecl;
	sourceThis.path = sourceClassDecl.path + "/this";
	destinationThis = destinationClassDecl;
	destinationThis.path = destinationClassDecl.path + "/this";
	
	map[loc,loc] swapped = (r1:dep1 | s1:call(id1, r1, methodDecl, dep1) <- differences, s2:call(id2, r2, decl, dep2) <- differencesR, id1 == id2, r1 == dep2, dep1 == r2);

	//check entry and exit points
	checked = {s1, s2 | s1:entryPoint(id1, methodDecl)			<- differences, s2:entryPoint(id2, decl) 							<- differencesR, id1 == id2}
	 		+ {s1, s2 | s1:exitPoint(id1, methodDecl) 			<- differences, s2:exitPoint(id2, decl) 							<- differencesR, id1 == id2}
			+ {s1, s2 | s1:read(id1, sourceThis, dep1) 			<- differences, s2:read(id2, newParam, dep2) 						<- (differencesR), id1 == id2}
			+ {s1, s2 | s1:read(id1, origParam, dep1) 			<- differences, s2:read(id2, destinationThis, dep2) 				<- (differencesR), id1 == id2}
			+ {s1, s2 | s1:change(id1, sourceClassDecl, dep1)	<- differences, s2:change(id2, destinationClassDecl, dep2) 			<- (differencesR), id2 == (swapped[id1] ? emptyId)}
			+ {s1, s2 | s1:call(id1, r1, methodDecl, dep1) 		<- differences, s2:call(id2, r2, decl, dep2) 						<- differencesR, id1 == id2, r1 == dep2, dep1 == r2}
			+ {s1, s2 | s1:call(id1, r1, methodDecl, dep1) 		<- differences, s2:call(id2, r2, decl, dep2) 						<- differencesR, id1 == id2, dep1 == dep2, r2 == (swapped[r1] ? emptyId)}
			;
	return ((differencesR + differences) - checked) == {};
}

//Configure refactoring
MethodCase getMovedMethodConfiguration(Declaration from:class(_, _, _, body), Declaration to, Declaration m:method(r, n, ps, exs, b)){
	//find the configuration if the method is static
	if(static() in (m@modifiers ? {})){
		println("The method is static! Move on ;)");
		receiver = createQualifiedClass(to@decl,m@src);
		newDecl = getNewMethodDeclaration(from@decl, to@decl, m, true, false);	
		return MethodCase::\static(newDecl, receiver);
	}
	
	//find the configuration if the target class is a parameter of the method
	for(p:parameter(simpleType(exp),pname,extr) <- ps){
		if(exp@decl == to@decl){
			println("The destination class is a parameter!");
			newDecl = getNewMethodDeclaration(from@decl, to@decl, m, false, true);
			int i = indexOf(ps,p);
			loc newParamDecl = p@decl;
			newParamDecl.path = newDecl.path + "/" + substring(p@decl.path,findLast(p@decl.path, "/")+1);
			return MethodCase::inParameters(newDecl, i, p@decl, newParamDecl);
		}
	}
	
	//find the configuration if the target class is a field of the source class
	pname = "param_param";
	for(/f:field(simpleType(exp), [v,*vs]) <- body){
		if(exp@decl == to@decl){
			println("The destination class is a field!");
			newDecl = getNewMethodDeclaration(from@decl, to@decl, m, false, false);
			fname = extractVariableNameFromDecl(v@decl);
			fieldExp = simpleName(fname)[@decl = v@decl][@src = generateId(m@src)][@typ = v@typ];
			param = Declaration::parameter(simpleType(createQualifiedName(from@decl)[@src = m@src]), pname, 0)[@src = m@src][@decl = |java+parameter:///|+newDecl.path+"/"+pname][@typ = from@typ];
			return MethodCase::inFields(newDecl, fieldExp, param);
		}
	}
	return notTransferable();
}

//Static method
Declaration adaptMethodsCode(MethodCase s:\static(decl, receiver), Declaration m:method(r, name, ps, exs, body)){
	from = getClassDeclFromMethod(m@decl);
	body = top-down-break visit(body){
		case q:qualifiedName(exp, _):{
			if(isField(q))
				insert replaceAccessor(q, receiver);
		}
		case s:simpleName(_):{
			if(s@decl == from)
				insert replaceAccessor(s, receiver);
		}
	}
	return method(r, name, ps, exs, body)[@decl = decl][@src = m@src][@typ = m@typ][@modifiers = m@modifiers];
}

Expression replaceAccessor(Expression s:simpleName(_), Expression receiver)
	= receiver[@src = s@src];
Expression replaceAccessor(Expression q:qualifiedName(exp, s), Expression receiver)
	= qualifiedName(replaceAccessor(exp, receiver), s)[@decl = q@decl][@typ = q@typ][@src = q@src];

Expression adaptMethodCall(MethodCase s:\static(decl, receiver), Expression m:methodCall(isSuper, name, args))
	= methodCall(isSuper, addGeneratedId(receiver), name, args)[@decl = decl][@typ = m@typ][@src = m@src];

Expression adaptMethodCall(MethodCase s:\static(decl, receiver), Expression m:methodCall(isSuper, rec, name, args)){
	return methodCall(isSuper, receiver[@src = rec@src], name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

//Method with the destination class as a parameter
Declaration adaptMethodsCode(MethodCase s:inParameters(loc decl, int index, loc origP, loc newP), Declaration m:method(r, name, ps, exs, body)){
	oldDecl = m@decl;
	from = getClassDeclFromMethod(m@decl);
	to = getClassDeclFromMethod(decl);
	
	ps = replaceWithNewParameter(ps, index, from, decl);
	body = renameParameterAndThis(body, m@decl, decl, origP, newP, from, to);
	return method(r, name, ps, exs, body)[@decl = decl][@src = m@src][@typ = m@typ][@modifiers = m@modifiers];
}

Expression adaptMethodCall(MethodCase s:inParameters(loc decl, int index, loc origP, loc newP), m:methodCall(isSuper, name, args)){
	from = getClassDeclFromMethod(decl);
	rec = args[index];
	if((index+1) < size(args))
		args = args[0..index]+[this()[@decl = from]]+args[index+1..];
	else
		args = args[0..index]+[this()[@decl = from]];
	return methodCall(isSuper, rec, name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

Expression adaptMethodCall(MethodCase s:inParameters(loc decl, int index, loc origP, loc newP), Expression m:methodCall(isSuper, rec, name, args)){
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
	return Declaration::parameter(simpleType(createQualifiedClass(from, exp@src)[@src = exp@src]), name, d)[@src = p@src][@decl = |java+parameter:///|+methodDecl.path+"/"+name][@typ = class(from,[])];
}

Statement renameParameterAndThis(Statement body, loc oldMethodDecl, loc newMethodDecl, loc paramDecl, loc newParamDecl, loc from, loc to){
	newParam = simpleName(extractVariableNameFromDecl(newParamDecl))[@decl = newParamDecl][@typ = class(from,[])];
	return top-down-break visit(body){
		case q:qualifiedName(_,_):{
			if(isField(q)){
				insert accessThroughVariable(q, newParam);
			}
			else if(getFirstAccessDecl(q) == paramDecl){
				insert insertAccessThroughThis(q, to);
			}
		}
		case f:fieldAccess(isSuper, exp, name) => convertFieldToQualified(f, newParam)
		case e:this() => newParam[@src = e@src]
		case e:simpleName(name):{
			if(e@decl == paramDecl){
				insert this()[@decl = paramDecl][@typ = e@typ][@src = e@src];
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


//Method with the destination class as a field of the source class
Declaration adaptMethodsCode(MethodCase s:inFields(decl, fieldExp, param), Declaration m:method(r, name, list[Declaration] ps, exs, body)){
	oldDecl = m@decl;
	paramDecl = param@decl;
	from = getClassDeclFromMethod(m@decl);
	
	newParam = simpleName(extractVariableNameFromDecl(param@decl))[@decl = param@decl][@typ = class(from,[])];	
	body = adaptCallsAndFields(body, decl, m@decl, from, fieldExp, newParam);
	return method(r, name, ps + [param[@decl = m@decl][@src = generateId(m@src)]], exs, body)[@decl = decl][@modifiers = m@modifiers];
}

Expression adaptMethodCall(MethodCase s:inFields(decl, fieldExp, param), Expression m:methodCall(isSuper, name, list[Expression] args)){
	from = getClassDeclFromMethod(decl);
	args += [\this()[@typ = class(from,[])]];
	return methodCall(isSuper, fieldExp[@src = m@src], name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

Expression adaptMethodCall(MethodCase s:inFields(decl, fieldExp, param), Expression m:methodCall(isSuper, rec, name, args)){	
	return methodCall(isSuper, qualifiedName(rec, fieldExp[@src = m@src]), name, args + [rec])[@decl = decl][@typ = m@typ][@src = m@src];
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
				insert qualifiedName(newParam, e)[@src = generateId(e@src)][@decl = e@decl][@typ = e@typ];
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
				insert methodCall(isSuper, qualifiedName(newParam[@src = generateId(m@src)], fieldExp[@src = m@src]), name, args)[@decl = newDecl][@typ = m@typ][@src = m@src];
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
				insert methodCall(isSuper, qualifiedName(rec, fieldExp[@src = generateId(m@src)]), name, args)[@decl = newDecl][@typ = m@typ][@src = m@src];
			}
			else
				fail;
		}
	}
}

Expression accessThroughVariable(Expression s:simpleName(_), Expression newParam)
	= qualifiedName(newParam[@src = generateId(s@src)], s)[@src = s@src][@src = s@src][@typ = s@typ]; 
Expression accessThroughVariable(Expression q:qualifiedName(exp,f), Expression newParam)
	= qualifiedName(accessThroughVariable(exp,newParam), f)[@src = q@src][@decl = q@decl][@typ = q@typ]; 
	
Expression convertFieldToQualified(Expression f:fieldAccess(_, t:this(), name), Expression newParam)
	= qualifiedName(newParam[@src = t@src], simpleName(name)[@decl = f@decl][@src = f@src][@typ = f@typ])[@decl = f@decl][@src = f@src][@typ = f@typ];
Expression convertFieldToQualified(Expression f:fieldAccess(_, exp, name), Expression newParam)
	= qualifiedName(convertFieldToQualified(exp, newParam), simpleName(name)[@decl = f@decl][@src = f@src][@typ = f@typ])[@decl = f@decl][@src = f@src][@typ = f@typ];

Expression insertAccessThroughThis(Expression q:qualifiedName(v:simpleName(_), s:simpleName(name)), loc to)
	= fieldAccess(false, \this()[@decl = to][@src = v@src][@typ = class(to,[])],name)[@decl = s@decl][@src = s@src][@typ = s@typ];
Expression insertAccessThroughThis(Expression q:qualifiedName(exp, s:simpleName(name)), loc to)
	= fieldAccess(false, insertAccessThroughThis(exp, to), name)[@decl = s@decl][@typ = s@typ][@src = s@src];
	
