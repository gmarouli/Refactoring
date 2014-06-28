module refactoring::rearranging_code::GenerateIds

import lang::java::jdt::m3::AST;
import IO;

int offset = 0;

anno loc Expression @ oldSrc;

Expression addGeneratedId(Expression exp){
	return top-down-break visit(exp){
		case e:simpleName(_) => e[@src = generateId(e@src)][@oldSrc = e@src]
		case e:super() => e[@src = generateId(e@src)][@oldSrc = e@src]
		case e:this() => e[@src = generateId(e@src)][@oldSrc = e@src]
		case e:methodCall(isSuper, name, arguments) => methodCall(isSuper, name, [addGeneratedId(arg) | arg <- arguments])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:e:methodCall(isSuper, receiver, name, arguments) =>
			methodCall(isSuper, addGeneratedId(receiver), name, [addGeneratedId(arg) | arg <- arguments])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\newObject(expr, t, args, c) =>
			\newObject(addGeneratedId(expr), t, [addGeneratedId(arg) | arg <-args], c)[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newObject(expr, t, args) =>
    		\newObject(addGeneratedId(expr), t, [addGeneratedId(arg) | arg <-args])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newObject(t, args, c) =>
    		\newObject(t, [addGeneratedId(arg) | arg <-args], c)[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newObject(t, args) =>
    		\newObject(t, [addGeneratedId(arg) | arg <-args])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newArray(t, ds, init) =>
    		\newArray(t, [addGeneratedId(d) | d <- ds], addGeneratedId(init))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:newArray(Type \type, list[Expression] dimensions) =>
			\newArray(t, [addGeneratedId(d) | d <- ds])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:arrayAccess(Expression array, Expression index) =>
			arrayAccess(addGeneratedId(array), addGeneratedId(index))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:qualifiedName(q, exp) => qualifiedName(addGeneratedId(q), addGeneratedId(exp))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\fieldAccess(isSuper, addGeneratedId(exp), name) => \fieldAccess(isSuper, exp, name)[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
   		case e:\fieldAccess(_, _) => e[@src = generateId(e@src)][@oldSrc = e@src]
   		case e:\assignment(lhs, op, rhs) => assignment(addGeneratedId(lhs), op, addGeneratedId(rhs))[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
	}
}

loc generateId(loc src){
	src.offset = offset;
	src.length = 0;
	offset+=1;
	return src;
}