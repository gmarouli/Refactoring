module refactoring::microrefactorings::MicroRefactorings

import refactoring::microrefactorings::GetInfo;
import lang::java::jdt::m3::AST;
import IO;
import List;

Declaration desugarSynchronizedMethod(Declaration targetMethod:method(r, n, p, exc, impl)){
	if(synchronized() in  (targetMethod@modifiers ? {})){
		return method(r, n, p, exc, encloseInSynchronized(targetMethod))[@modifiers = (targetMethod@modifiers - \synchronized())][@src = targetMethod@src][@decl = targetMethod@decl][@typ = targetMethod@typ];
	}
	else{
		return targetMethod;
	}
		
}
	
Declaration sugarSynchronizedMethod(Declaration m:method(r, n, p, exc, impl)){
	switch(impl){
		case s:synchronizedStatement(l,body):{
			if(static() in (method@modifiers ? {}))
				return m;
			else
				return method(r, n, p, exc, body)[@modifiers = (m@modifiers + /synchronized())][@src = m@src][@decl = m@decl][@origDecl = m@origDecl][@typ = m@typ];
		}
		default:{
			return m;
		}	
	}
}

tuple[bool, loc, int, int] accessLimits(Statement b, loc local){
	visit(b){
		case s:block(stmts):{
			<found, st, end> = points(stmts, local);
			if(found)
				return <true, s@src, st, end>;
		}
	}
	return <false, |empty:///|, -1, -1>;
}

tuple[bool, int, int] points(list[Statement] stmts, loc local){
	found = false;
	starting = -1;
	ending = -1;
	for(stmt <- stmts){
		if(!found){
			<found, starting, ending> = isDeclarationOf(stmt, local);
		}
		else{
			visit(stmt){				
				case e:simpleName(_):{
					if(e@decl == local){
						ending = e@src.offset + e@src.length;
					}
				}
			}
		}
	}
	return <found, starting, ending>;
}

tuple[bool, int, int] isDeclarationOf(Statement s:declarationStatement(variables(_, frags)), loc local){
	for(f <- frags){
		if(f@decl == local){
			return <true, f@src.offset, f@src.offset + f@src.length>;
		}
	}
}

Statement insertIntoBlock(Statement b, loc local, loc src, int starting, int ending){
	contents = [];
	return top-down-break visit(b){
		case s:block(stmts):{
			if(s@src == src){ 
				updatedContents = for(stmt <- stmts){
					if((stmt@src.offset + stmt@src.length) < starting)
						append(stmt);
					else if(stmt@src.offset > ending){
						if(contents != []){
							bSrc = s@src;
							bSrc.offset = starting;
							bSrc.length = ending - starting;
							
							append(block(contents)[@src = bSrc]);
							contents = [];
						}
						append(stmt);
					}
					else{
						if(contents == []){
							<otherDecl, init> = splitDeclarations(stmt, local);
							append(otherDecl);
							contents = [init];
						}
						else
							contents += [stmt];
					}
				}
				if(size(updatedContents) == 1)
					insert b;
				else
					insert block(updatedContents)[@src = s@src];
			}
			else{
				fail;
			}
		}
	}
}

tuple[Statement, Statement] splitDeclarations(Statement s:declarationStatement(variables(t, frags)), loc local){
	Statement init = Statement::empty();
	Statement otherDecl = Statement::empty();
	frags =	for(f <- frags){
		if(f@decl == local){
			init = getAssignmentFromDeclaration(f);
		}
		else{
			append(f);
		}
	}
	if(frags != [])
		otherDecl = declarationStatement(variables(t, frags))[@src = s@src];
	return <otherDecl, init>;
}

Statement getAssignmentFromDeclaration(Expression v:variable(name, _, init))
	= expressionStatement(assignment(simpleName(name)[@decl = v@decl][@typ = v@typ][@src = v@src], "=", init)[@src = v@src][@typ = v@typ])[@src = v@src];
default Expression getAssignmentFromDeclaration(Expression v)
	= Statement::empty();

Statement extractBlock(Statement b, loc local){
	<found, blockSrc, starting, ending> = accessLimits(b, local);
	println("Found in <blockSrc>, [<starting>, <ending>]");
	if(found)
		return insertIntoBlock(b, local, blockSrc, starting, ending);
	else{
		println("Error: Local variable <local> not found!");
		return b;
	}
}

Declaration adaptMethodCall(loc targetMethod, loc sourceClass, loc destinationClass, Statement m:methodCall(isSuper, name, args)){
	return m;
}

Declaration adaptMethodCall(loc targetMethod, loc sourceClass, loc destinationClass, Statement m:methodCall(isSuper, rcv, name, args)){
	return m;
}
