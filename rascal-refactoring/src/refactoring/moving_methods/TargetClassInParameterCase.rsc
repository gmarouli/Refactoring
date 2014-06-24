module refactoring::moving_methods::TargetClassInParameterCase

import List;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::moving_methods::MoveMethod;
import refactoring::microrefactorings::GetInfo;

Declaration adaptMethod(MethodCase s:inParameters(loc decl, int index), Declaration m:method(r, name, ps, exs, body)){
	oldDecl = m@decl;
	paramDecl = ps[index]@decl;
	from = getClassDeclFromMethod(m@decl);
	ps = replaceWithNewParameter(ps, index, from, decl);
	body = renameParameterAndThis(body, paramDecl, ps[index]@decl, from);
	body = adaptMethodCalls(s, m@decl, body);
	return method(r, name, ps, exs, body)[@decl = decl][@modifiers = m@modifiers];
}

Statement adaptMethodCalls(MethodCase s:inParameters(loc decl, int index), loc oldDecl, Statement body){
	return visit(body){
		case m:methodCall(isSuper, name, args):{
			if(m@decl == oldDecl){
				insert adaptMethodCall(s, m);
			}
			else
				fail;
		}
		case m:methodCall(isSuper, rec, name, args):{
			if(m@decl == oldDecl){
				adaptMethodCall(s, m);
			}
			else
				fail;
		}
	}
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

Statement renameParameterAndThis(Statement body, loc paramDecl, loc newParamDecl, loc from){
	newParam = simpleName(extractVariableNameFromDecl(newParamDecl))[@decl = newParamDecl][@typ = class(from,[])];
	
	return top-down-break visit(body){
		case q:qualifiedName(_,_) => q
		case e:this():{
			return newParam[@src = e@src];
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
			args = for(arg <- args){
				expressionStatement(arg) = renameParameterAndThis(expressionStatement(arg), paramDecl, newParamDecl, from);
				append(arg);
			}
			insert methodCall(isSuper, newParam, name, args)[@decl = m@decl][@typ = m@typ][@src = m@src];
		}
	}
}