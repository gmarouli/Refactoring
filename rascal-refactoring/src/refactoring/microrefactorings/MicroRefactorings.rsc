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

bool isDeclarationOf(Statement s:declarationStatement(variables(_, frags)), loc local){
	for(f <- frags){
		if(f@decl == local){
			return true;
		}
	}
}
default bool isDeclarationOf(Statement s, loc local)
	= false;

tuple[Statement, Declaration] addInASynchronizedBlock(Statement b, loc local, Expression l){
	loc bSrc = findBlockContainingLocal(b, local);
	Declaration removed;
	b = top-down-break visit(b){
		case s:block(stmts):{
			if(s@src == bSrc){
				<stmts1, newBlock, stmts2, removed> = extractBlock(s, local);
				newBlock = synchronizedStatement(l, newBlock)[@src = newBlock@src];
				if(stmts1 != [] || stmts2 != []){
					insert block(stmts1 + [newBlock] + stmts2)[@src = bSrc];
				}
				else{
					insert newBlock[@src = bSrc];
				}
			}
			else
				fail;
		}
	}
	return <b,removed>;
}

tuple[list[Statement], Statement, list[Statement], Declaration] extractBlock(Statement s:block(stmts), loc local){
	list[Statement] contents = [];
	list[Statement] unknown = [];
	bool accessed = false;
	loc bSrc = s@src;
	Declaration removed;
	stmts = for(stmt <- stmts){
		if(isDeclarationOf(stmt, local)){
			<otherDecl, init, removed> = splitDeclarations(stmt, local);
			if(otherDecl != Statement::empty())
				append(otherDecl);
			bSrc = s@src;
			bSrc.offset = 0;
			if(init != Statement::empty()){
				contents = [init];
				bSrc.offset = init@src.offset;
				bSrc.begin.line = init@src.begin.line;
				bSrc.begin.column = init@src.begin.column;
				accessed = true;
			}
	  	}
		else if(!accessed){
		  	append(stmt);
		}
		else{
			if(containsLocal(stmt, local)){
				contents += unknown + [stmt];
				unknown = [];
				if(bSrc.offset <= 0){
					bSrc.offset = stmt@src.offset;
					bSrc.begin.line = stmt@src.begin.line;
					bSrc.begin.column = stmt@src.begin.column;
				}
				bSrc.length = stmt@src.offset + stmt@src.length - bSrc.offset;
				bSrc.end.line = stmt@src.end.line;
				bSrc.end.column = stmt@src.end.column;
			}
			else
				unknown += [stmt];
		}
	}
	return <stmts,block(contents)[@src = bSrc],unknown, removed>;
}

bool containsLocal(Statement stmt, loc local){
	visit(stmt){				
		case e:simpleName(_):{
			if(e@decl == local){
				return true;
			}
		}
	}
	return false;
}

loc findBlockContainingLocal(Statement b, loc local){
	visit(b){
		case s:block(stmts):{
			for(stmt <- stmts){
				if(isDeclarationOf(stmt, local))
					return s@src;
			}
		}
	}
	throw "Error: Local variable <local> was not found!";
}

tuple[Statement, Statement, Declaration] splitDeclarations(Statement s:declarationStatement(variables(t, frags)), loc local){
	Statement init = Statement::empty();
	Statement otherDecl = Statement::empty();
	Declaration removed;
	frags =	for(f <- frags){
		if(f@decl == local){
			init = getAssignmentFromDeclaration(f);
			removed = createVariableDeclaration(t,f);
		}
		else{
			append(f);
		}
	}
	if(frags != [])
		otherDecl = declarationStatement(variables(t, frags))[@src = s@src];
	return <otherDecl, init, removed>;
}

Declaration createVariableDeclaration(Type t, Expression v:variable(name, d, _))
	= Declaration::field(t,[variable(name,d)])[@modifiers = [\private()]];
	
Declaration createVariableDeclaration(Type t, Expression v:variable(name, d))
	= Declaration::field(t,[v])[@modifiers = [\private()]];

Statement getAssignmentFromDeclaration(Expression v:variable(name, _, init))
	= expressionStatement(assignment(simpleName(name)[@decl = v@decl][@typ = v@typ][@src = v@src], "=", init)[@src = v@src][@typ = v@typ])[@src = v@src];
default Expression getAssignmentFromDeclaration(Expression v)
	= Statement::empty();

Declaration adaptMethodCall(loc targetMethod, loc sourceClass, loc destinationClass, Statement m:methodCall(isSuper, name, args)){
	return m;
}

Declaration adaptMethodCall(loc targetMethod, loc sourceClass, loc destinationClass, Statement m:methodCall(isSuper, rcv, name, args)){
	return m;
}
