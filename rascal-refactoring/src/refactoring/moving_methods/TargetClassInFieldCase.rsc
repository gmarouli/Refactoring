module refactoring::moving_methods::TargetClassInFieldCase

import List;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::moving_methods::MoveMethod;
import refactoring::microrefactorings::GetInfo;

Declaration adaptMethod(MethodCase s:inFields(decl, field, param), Declaration m:method(r, name, ps, exs, body)){
	oldDecl = m@decl;
	paramDecl = param@decl;
	from = getClassDeclFromMethod(m@decl);
	ps += param;
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

