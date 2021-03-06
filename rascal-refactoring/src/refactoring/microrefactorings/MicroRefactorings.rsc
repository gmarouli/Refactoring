module refactoring::microrefactorings::MicroRefactorings

import refactoring::microrefactorings::GetInfo;
import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;
import lang::java::jdt::m3::AST;
import IO;
import List;
import lang::sdfg::converter::Java2SDFG;
import lang::java::m3::TypeSymbol;
import refactoring::rearranging_code::GenerateIds;

Declaration addMethod(Declaration targetClass:class(name, ext, impl, body), Declaration target){
	return class(name, ext, impl, body+[target])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];	
}
			
Declaration removeMethod(Declaration targetClass:class(name, ext, impl, body), loc targetMethod){
	return class(name, ext, impl, [d | d <- body, isTargetMethod(d, targetMethod)])[@modifiers = targetClass@modifiers][@src = targetClass@src][@decl = targetClass@decl][@typ = targetClass@typ];
}

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

set[Declaration] desugarAccessToFields(set[Declaration] asts, loc methodDecl){
	return top-down-break visit(asts){
		case m:method(r, n, ps, exs, impl):{
			if(m@decl == methodDecl){
				if(Modifier::static() in (m@modifiers ? [])){
					impl = desugarQualifiedName(impl,getClassDeclFromMethod(m@decl));
				}
				else{
					impl = desugarThis(impl);
				}
				insert Declaration::method(r, n, ps, exs, impl)[@decl = m@decl][@typ = m@typ][@src = m@src][@modifiers = m@modifiers];
			}
		}
	}
}

Statement desugarQualifiedName(Statement impl, loc from){
	return top-down-break visit(impl){
		case q:qualifiedName(exp, _):{
			if(isField(q))
				insert desugarQualifiedName(q, from);
		}
		case s:simpleName(_):{
			if(isField(s))
				insert desugarQualifiedName(s, from);
		}
		case m:methodCall(isS, name, args) =>
			methodCall(isS, simpleName(substring(from.path,findLast(from.path,"/")))[@decl = from][@src = generateId(s@src)][@typ = createType(from)], name ,args)[@decl = m@decl][@typ = m@typ][@src = m@src]
	}
}

Expression desugarQualifiedName(Expression q:qualifiedName(exp, s), loc from)
	= qualifiedName(desugarQualifiedName(exp, from), s)[@decl = q@decl][@typ = q@typ][@src = q@src];
Expression desugarQualifiedName(Expression s:simpleName(_), loc from)
	= qualifiedName(simpleName(substring(from.path,findLast(from.path,"/")))[@decl = from][@src = generateId(s@src)][@typ = createType(from)], s)[@decl = s@decl][@typ = s@typ][@src = s@src];
	
Statement desugarThis(Statement impl){
	return top-down-break visit(impl){
		case q:qualifiedName(exp, _):{
			if(isField(q))
				insert desugarThis(q);
		}
		case s:simpleName(_):{
			if(isField(s))
				insert desugarThis(s);
		}
		case m:methodCall(isS, name, args) =>
			methodCall(isS, \this()[@typ = class(getClassDeclFromMethod(s@decl),[])][@decl = getClassDeclFromMethod(s@decl)], name ,args)[@decl = m@decl][@typ = m@typ][@src = m@src]
	}
}


Expression desugarThis(Expression s:simpleName(name))
	= fieldAccess(false, \this()[@typ = class(|java+class:///|+extractClassName(s@decl),[])][@decl = |java+class:///|+extractClassName(s@decl)][@src = generateId(s@src)],name)[@src = s@src][@decl = s@decl][@typ = s@typ];
Expression desugarThis(Expression q:qualifiedName(exp, s:simpleName(name)))
	= fieldAccess(false, desugarThis(exp), name)[@src = s@src][@decl = s@decl][@typ = s@typ];


bool isDeclarationOf(Statement s:declarationStatement(variables(_, frags)), loc local){
	for(f <- frags){
		if(f@decl == local){
			return true;
		}
	}
	return false;
}
default bool isDeclarationOf(Statement s, loc local)
	= false;

tuple[Statement, Declaration] encloseInASynchronizedBlock(Statement b, loc local, loc fieldDecl, Expression l){
	loc bSrc = findBlockContainingLocal(b, local);
	Declaration removed;
	b = top-down-break visit(b){
		case s:block(stmts):{
			if(s@src == bSrc){
				<stmts1, newBlock, stmts2, removed> = extractBlock(s, local, fieldDecl);
				newBlock = synchronizedStatement(l[@src = newBlock@src], newBlock)[@src = newBlock@src];
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

tuple[list[Statement], Statement, list[Statement], Declaration] extractBlock(Statement s:block(stmts), loc local, loc fieldDecl){
	list[Statement] contents = [];
	list[Statement] unknown = [];
	bool accessed = false;
	loc bSrc = s@src;
	Declaration removed;
	stmts = for(stmt <- stmts){
		if(isDeclarationOf(stmt, local)){
			<otherDecl, init, removed> = splitDeclarations(stmt, local, fieldDecl);
			if(otherDecl != Statement::empty())
				append(otherDecl);
			bSrc = s@src;
			bSrc.offset = 0;
			if(init != Statement::empty()){
				contents = [init];
				bSrc.offset = init@src.offset;
				bSrc.begin.line = init@src.begin.line;
				bSrc.begin.column = init@src.begin.column;
			}
			accessed = true;
	  	}
		else if(!accessed){
		  	append(stmt);
		}
		else{
			<stmt, containsLocal> = convertLocalDeclToFieldDecl(stmt, local, fieldDecl); 
			if(containsLocal){
				if(bSrc.offset <= 0){
					bSrc.offset = stmt@src.offset;
					bSrc.begin.line = stmt@src.begin.line;
					bSrc.begin.column = stmt@src.begin.column;
				}
				contents += unknown + [stmt];
				unknown = [];
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

tuple[Statement, bool] convertLocalDeclToFieldDecl(Statement stmt, loc local, loc fieldDecl){
	bool found = false;
	stmt = visit(stmt){				
		case e:simpleName(_):{
			if(e@decl == local){
				found = true;
				insert e[@decl = fieldDecl];
			}
			else
				fail;
		}
	}
	return <stmt,found>;
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

tuple[Statement, Statement, Declaration] splitDeclarations(Statement s:declarationStatement(vars:variables(t, frags)), loc local, loc fieldDecl){
	Statement init = Statement::empty();
	Statement otherDecl = Statement::empty();
	Declaration removed;
	frags =	for(f <- frags){
		if(f@decl == local){
			init = getAssignmentFromDeclaration(f, s@src, fieldDecl);
			removed = createVariableDeclaration(t,f, fieldDecl);
		}
		else{
			append(f);
		}
	}
	if(frags != [])
		otherDecl = declarationStatement(variables(t, frags))[@src = s@src];
	return <otherDecl, init, removed>;
}

Declaration createVariableDeclaration(Type t, Expression v:variable(name, d, _), loc fieldDecl)
	= Declaration::field(t,[variable(name,d)[@decl = fieldDecl][@typ = v@typ][@src = v@src]])[@modifiers = [\private()]];
	
Declaration createVariableDeclaration(Type t, Expression v:variable(name, d), loc fieldDecl)
	= Declaration::field(t,[v[@decl = fieldDecl]])[@modifiers = [\private()]];

Statement getAssignmentFromDeclaration(Expression v:variable(name, _, init), loc assignSrc, loc fieldDecl)
	= expressionStatement(assignment(simpleName(name)[@decl = fieldDecl][@typ = v@typ][@src = v@src], "=", init)[@src = v@src][@typ = v@typ])[@src = assignSrc];
default Statement getAssignmentFromDeclaration(Expression v, loc assignSrc, loc fieldDecl)
	= Statement::empty();
