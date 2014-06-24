module refactoring::moving_methods::TargetClassInFieldCase

import List;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::moving_methods::MoveMethod;
import refactoring::microrefactorings::GetInfo;

Declaration adaptMethod(MethodCase s:inFields(decl, field, param), Declaration m:method(r, name, ps, exs, body)){
	oldDecl = m@decl;
	paramDecl = param@decl;
	ps += param;
	body = adaptInnerMethodCalls(s, m@decl, body);
	return method(r, name, ps + [param[@decl = m@decl]], exs, body)[@decl = decl][@modifiers = m@modifiers];
}

Statement adaptInnerMethodCalls(MethodCase s:inFields(decl, field, _), Expression param, loc oldDecl, Statement body){
	from = getClassDeclFromMethod(m@decl);
	//return visit(body){
	//	case e:qualifiedName(exp,_):{
	//		if(firstDeclarationOfQualifiedName() == from){
	//			insert addFieldToQualifiedName(e, param);
	//		}
	//	}
	//}
}

Expression adaptMethodCall(MethodCase s:inFields(decl, field, param), m:methodCall(isSuper, name, args)){
	return methodCall(isSuper, rec, name, args + [param])[@decl = decl][@typ = m@typ][@src = m@src];
}

Expression adaptMethodCall(MethodCase s:inFields(decl, field, param:parameter(_,name,_)), Expression m:methodCall(isSuper, rec, name, args)){
	return methodCall(isSuper, newRec, name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

