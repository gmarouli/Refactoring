module refactoring::rearranging_code::GenerateIds

import lang::java::jdt::m3::AST;
import IO;

int offset = 0;

anno loc Expression @ oldSrc;

Expression addGeneratedId(Expression inlinedExp){
	return top-down-break visit(inlinedExp){
		case e:arrayAccess(Expression array, Expression index) =>
			arrayAccess(addGeneratedId(array), addGeneratedId(index))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\newArray(t, ds, init) =>
    		\newArray(t, [addGeneratedId(d) | d <- ds], addGeneratedId(init))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:newArray(Type \type, list[Expression] dimensions) =>
			\newArray(t, [addGeneratedId(d) | d <- ds])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\arrayInitializer(init) => \arrayInitializer([addGeneratedId(i) | i <- init])[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\assignment(lhs, op, rhs) => assignment(addGeneratedId(lhs), op, addGeneratedId(rhs))[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\cast(t,exp) => \cast(t,addGeneratedId(exp))[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\newObject(expr, t, args, c) =>
			\newObject(addGeneratedId(expr), t, [addGeneratedId(arg) | arg <-args], c)[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newObject(expr, t, args) =>
    		\newObject(addGeneratedId(expr), t, [addGeneratedId(arg) | arg <-args])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newObject(t, args, c) =>
    		\newObject(t, [addGeneratedId(arg) | arg <-args], c)[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:\newObject(t, args) =>
    		\newObject(t, [addGeneratedId(arg) | arg <-args])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
    	case e:qualifiedName(q, exp) => qualifiedName(addGeneratedId(q), addGeneratedId(exp))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:conditional(cond, ifE, elseE) => conditions(addGeneratedId(cond),addGeneratedId(ifE),addGeneratedId(elseE))[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\fieldAccess(isSuper, addGeneratedId(exp), name) => \fieldAccess(isSuper, exp, name)[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:methodCall(isSuper, name, arguments) => methodCall(isSuper, name, [addGeneratedId(arg) | arg <- arguments])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:methodCall(isSuper, receiver, name, arguments) =>
			methodCall(isSuper, addGeneratedId(receiver), name, [addGeneratedId(arg) | arg <- arguments])[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:\bracket(exp) => \bracket(addGeneratedId(exp))[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case e:infix(lhs, op, rhs, exts) => infix(addGeneratedId(lhs), op, addGeneratedId(rhs), [addGeneratedId(ext) | ext <- exts])[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
  		case e:\postfix(operand, operator) => postfix(addGeneratedId(operand), operator)[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
   		case e:\prefix(operator, operand) => prefix(operator, addGeneratedId(operand))[@typ = e@typ][@src = generateId(e@src)][@oldSrc = e@src]
		case Expression e => e[@oldSrc = e@src][@src = generateId(e@src)]
	}
}

Expression addGeneratedId(Expression inlinedExp, loc src){
	return top-down-break visit(inlinedExp){
		case e:arrayAccess(Expression array, Expression index) =>
			arrayAccess(addGeneratedId(array, src), addGeneratedId(index, src))[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
		case e:\newArray(t, ds, init) =>
    		\newArray(t, [addGeneratedId(d,src) | d <- ds], addGeneratedId(init, src))[@decl = e@decl][@typ = e@typ][@src = generateId(e@src)]
		case e:newArray(Type \type, list[Expression] dimensions) =>
			\newArray(t, [addGeneratedId(d,src) | d <- ds])[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
		case e:\arrayInitializer(init) => \arrayInitializer([addGeneratedId(i,src) | i <- init])[@typ = e@typ][@src = generateId(src)]
		case e:\assignment(lhs, op, rhs) => assignment(addGeneratedId(lhs,src), op, addGeneratedId(rhs,src))[@typ = e@typ][@src = generateId(src)]
		case e:\cast(t,exp) => \cast(t,addGeneratedId(exp,src))[@typ = e@typ][@src = generateId(src)]
		case e:\newObject(expr, t, args, c) =>
			\newObject(addGeneratedId(expr,src), t, [addGeneratedId(arg,src) | arg <-args], c)[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
    	case e:\newObject(expr, t, args) =>
    		\newObject(addGeneratedId(expr,src), t, [addGeneratedId(arg,src) | arg <-args])[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
    	case e:\newObject(t, args, c) =>
    		\newObject(t, [addGeneratedId(arg,src) | arg <-args], c)[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
    	case e:\newObject(t, args) =>
    		\newObject(t, [addGeneratedId(arg,src) | arg <-args])[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
    	case e:qualifiedName(q, exp) => qualifiedName(addGeneratedId(q,src), addGeneratedId(exp,src))[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
		case e:conditional(cond, ifE, elseE) => conditions(addGeneratedId(cond,src),addGeneratedId(ifE,src),addGeneratedId(elseE,src))[@typ = e@typ][@src = generateId(src)]
		case e:\fieldAccess(isSuper, addGeneratedId(exp,src), name) => \fieldAccess(isSuper, exp, name)[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
		case e:methodCall(isSuper, name, arguments) => methodCall(isSuper, name, [addGeneratedId(arg,src) | arg <- arguments])[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
		case e:methodCall(isSuper, receiver, name, arguments) =>
			methodCall(isSuper, addGeneratedId(receiver,src), name, [addGeneratedId(arg,src) | arg <- arguments])[@decl = e@decl][@typ = e@typ][@src = generateId(src)]
		case e:\bracket(exp) => \bracket(addGeneratedId(exp,src))[@typ = e@typ][@src = generateId(src)]
		case e:infix(lhs, op, rhs, exts) => infix(addGeneratedId(lhs,src), op, addGeneratedId(rhs,src), [addGeneratedId(ext,src) | ext <- exts])[@typ = e@typ][@src = generateId(src)]
  		case e:\postfix(operand, operator) => postfix(addGeneratedId(operand,src), operator)[@typ = e@typ][@src = generateId(src)]
   		case e:\prefix(operator, operand) => prefix(operator, addGeneratedId(operand,src))[@typ = e@typ][@src = generateId(src)]
		case Expression e => e[@src = generateId(src)]
	}
}

loc generateId(loc src){
	src.offset = offset;
	src.length = 0;
	offset+=1;
	return src;
}