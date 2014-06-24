module refactoring::moving_methods::StaticMethodCase

import lang::java::jdt::m3::AST;
import refactoring::moving_methods::MoveMethod;
import refactoring::microrefactorings::GetInfo;

Declaration adaptMethodsCode(MethodCase s:\static(decl, receiver), Declaration m:method(r, name, ps, exs, body)){
	from = getClassDeclFromMethod(m@decl);
	body = adaptMethodCalls(s, m@decl, body);
	body = top-down-break visit(body){
		case q:qualifiedName(_,_):{
			if(isFieldOf(q, from)){
				insert accessThroughVariable(q, receiver);//TODO : is this working?
			}
		}
		case e:simpleName(name):{
			if(isFieldOf(e, from)){
				insert qualifiedName(reveiver, e)[@src = e@src][@decl = e@decl][@typ = e@typ];
			}
		}
	}
	return method(r, name, ps, exs, body)[@decl = decl][@modifiers = m@modifiers];
}

Expression adaptMethodCall(MethodCase s:\static(decl, receiver), Expression m:methodCall(isSuper, name, args)){
	return methodCall(isSuper, receiver, name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}

Expression adaptMethodCall(MethodCase s:\static(decl, receiver), Expression m:methodCall(isSuper, rec, name, args)){
	return methodCall(isSuper, receiver, name, args)[@decl = decl][@typ = m@typ][@src = m@src];
}