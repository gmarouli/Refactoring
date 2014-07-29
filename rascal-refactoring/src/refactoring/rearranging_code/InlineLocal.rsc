module refactoring::rearranging_code::InlineLocal

import IO;
import Set;
import Map;
import String;

import PrettyPrint;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;
import lang::sdfg::converter::Java2SDFG;
import lang::sdfg::converter::util::Getters;

import refactoring::microrefactorings::GetInfo;
import refactoring::microrefactorings::MicroRefactorings;
import refactoring::rearranging_code::GenerateIds;

data HelpingExp = helpingExp(Expression contExp, Expression brExp, Expression retExp, map[str, Expression] exs);

set[Declaration] inlineLocal(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	
	//Collect synchronized methods
	p = createDFG(asts);
	synchronizedMethods = getSynchronizedMethods(p, getCallGraph(asts));
	
	map[loc, loc] replacementIds = ();
	
	refactoredAsts = visit(asts){
		case m:method(r, n, ps, exs, b):{
			if(m@decl == targetedMethodDecl){
				<b, replacementIds, inlinedBy> = inlineLocal(b, local, {}, replacementIds, inlinedBy, synchronizedMethods);
				insert method(r, n, ps, exs, b)[@src = m@src][@decl = m@decl][@typ = m@typ];
			}
			else
				fail;
		}
	}
	
	pR = createDFG(refactoredAsts);
		
	if(checkInlineLocal(p,pR, local, replacementIds, inlinedBy)){
		println("Refactoring InlineLocal successful!");
		return refactoredAsts;
	}
	else{
		println("Refactoring failed!");
		return asts;
	}
}

bool checkInlineLocal(Program p, Program pR, loc local, map[loc,loc] replacementIds){
	differences = p.stmts - pR.stmts;
	differencesR = pR.stmts - p.stmts;
	mapIds = ();
	for(s <- differences + differencesR )
		mapIds[getIdFromStmt(s)] = mapIds[getIdFromStmt(s)] ? {} + {s};
	iprintln(mapIds);
	checked = {s,generateOriginal(s,replacementIds) | s <- differencesR, generateOriginal(s,replacementIds) in p.stmts, verifyDependency(s), inlinedBy};
	differences -= checked;
	checked += {s,																	//assign
				sRead,									//read local
				sAssign,	//assign local
				sR
			|	s <- differences, getVarFromStmt(s) != local, bprintln(s),
				sRead <- mapIds[getDependencyFromStmt(s)] ? {},									//assign
				getVarFromStmt(sRead) == local, 								//read local
				sAssign <- mapIds[getDependencyFromStmt(sRead)],
				sR <- differencesR,
				getIdFromStmt(sR) == getIdFromStmt(s),
				getDependencyFromStmt(sAssign) == getOriginalId(replacementIds, getDependencyFromStmt(sR))	//read j?
			};

	//checked += findUnusedStmt(differences, p.stmts,{});
	iprintln((differences + differencesR) - checked);
	println("Differences: <size((differences + differencesR) - checked)>");
	return ((differences + differencesR) - checked) == {};
}


bool verifyDependency(Stmt s:read(id, var, dep), inlinedBy){
	
}

Stmt generateOriginal(Stmt s:read(id, var, dep), map[loc, loc] replacementIds)
	= read(getOriginalId(replacementIds, id), var, getOriginalId(replacementIds, dep));

Stmt generateOriginal(Stmt s:assign(id, var, dep), map[loc, loc] replacementIds)
	= assign(getOriginalId(replacementIds, id), var, getOriginalId(replacementIds, dep));

Stmt generateOriginal(Stmt s:call(id, r, m, dep), map[loc, loc] replacementIds)
	= read(getOriginalId(replacementIds, id), getOriginalId(replacementIds, r), m, getOriginalId(replacementIds, dep));

Stmt generateOriginal(Stmt s:create(id, c, dep), map[loc, loc] replacementIds)
	= read(getOriginalId(replacementIds, id), c, getOriginalId(replacementIds, dep));
	
Stmt generateOriginal(Stmt s:acquireLock(id, var, dep), map[loc, loc] replacementIds)
	= read(id, var, getOriginalId(replacementIds, dep));

Stmt generateOriginal(Stmt s:releaseLock(id, var, dep), map[loc, loc] replacementIds)
	= read(id, var, getOriginalId(replacementIds, dep));
	
Stmt generateOriginal(Stmt s:entryPoint(id, m), map[loc, loc] replacementIds)
	= s;
Stmt generateOriginal(Stmt s:exitPoint(id, m), map[loc, loc] replacementIds)
	= s;

	
loc getOriginalId(map[loc,loc] replacementIds, loc id)
	= replacementIds[id] ? id;

set[loc] getRefactoredId(map[loc,set[loc]] replacementIds, loc id)
	= replacementIds[id] ? {id};

bool isAssign(Stmt e:assign(_,_,_))
	= true;
default bool isAssign(Stmt e)
	= false;
	
tuple[Statement, map[loc,loc], map[loc,set[loc]]] inlineLocal(Statement blockStmt, loc local, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	loc targetBlock = findBlockContainingLocal(blockStmt, local);
	blockStmt = top-down-break visit(blockStmt){
		case s:block(stmts):{
			if(s@src == targetBlock){
				<s, exp, replacementVariables, replacementIds, inlinedBy, _> = inlineLocalInStatement(s, local, Expression::null(), replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
				if(containsFieldsOrMethods(replacementVariables))
					println("Warning: this refactoring inlined code that contained shared variables (fields) or method calls. In concurrent execution the value assigned from inlining could be different.");
				insert s;
			}
			else
				fail;
		}
	}
	return <blockStmt, replacementIds, inlinedBy>;
}	

////assert(Expression expression)
//tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	return gatherStmtFromStatements(m, \assert(exp, Expression::null()), env, volatileFields, actionsInPath, stmts);
//}
//
////assert(Expression expression, Expression message)
//tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp, message), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInPath += extractAcquireAction(potential, volatileFields);
//	
//	<stmts, potential, envM, exsM> = gatherStmtFromExpressions(m, message, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInExitPath += extractAcquireAction(potential, volatileFields);
//	exs = mergeState(exs, exsM);
//	//the volatile access from the message are not counted since if the message appears nothing else is going to be executed
//	//The assert is a possible an exit point, in case of finally we can see it as a return
//	env = merge(env,envM);
//	return <stmts, env, initializeReturnEnvironment(env), actionsInPath, initializeAcquireActionsFromReturn(actionsInExitPath), exs>;
//}
//
//block(list[Statement] statements)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:block(sB), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	HelpingExp extra = helpingExp(Expression::null(),Expression::null(),Expression::null(),());
	Expression newExp = exp;
	broken = false;
	sB = for(stmt <- sB){
		<stmt, newExp, replacementVariables, replacementIds, newExtra> = inlineLocalInStatement(stmt, local, newExp, replacementVariables, replacementIds, synchronizedMethods);
		if(!broken){
			exp = newExp;
			extra = updateExtra(extra, newExtra);
		}
		if(breakingControlFlow(stmt))
			broken = true;
		append(stmt);
	}
	return <block(sB)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//break()
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\break(), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), exp, Expression::null(), ())>;

//break("")
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\break(""), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), exp, Expression::null(), ())>;

//break(str label)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\break(exp), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	if(exp == "")
		fail;
	assert false : "Labeled statement (break) found!!!";
	return <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), exp, Expression::null(), ())>;
}

//continue()
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\continue(), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(exp, Expression::null(), Expression::null(), ())>;
	
//continue(str label)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\continue(exp), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	assert false : "Labeled statement (continue) found!!!";
	return <s, Expression::null(), replacementVariables, replacementIds, helpingExp(exp, Expression::null(), Expression::null(), ())>;
}

//do(Statement body, Expression condition)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\do(b, cond), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<b, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(b, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	if(Expression::null() := exp){
		exp = getContinueExp(extra);
	}
	<cond, exp, replacementVariables, replacementIds, extra> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);

	if(Expression::null() := exp){
		exp = getBreakExp(extra);
	}	
	return <\do(b, cond)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//foreach(Declaration parameter, Expression collection, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\foreach(parameter, collection, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<collection, exp, replacementVariables, replacementIds, extra> = inlineLocal(collection, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	if(Expression::null() := exp){
		exp = getBreakExp(extra);
	}	
	return <\foreach(parameter, collection, body)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\for(init, cond, updaters, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	init = for(i <- init){
		<temp, exp, replacementVariables, replacementIds> = inlineLocal(i, local, exp, replacementVariables, replacementIds, synchronizedMethods);
		if(!isLocalAssignment(i, local))
			append(temp);
	}
	<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	updaters = for(u <- updaters){
		<temp, exp, replacementVariables, replacementIds> = inlineLocal(u, local, exp, replacementVariables, replacementIds, synchronizedMethods);
		if(!isLocalAssignment(u, local))
			append(temp);
	}
	
	if(Expression::null() := exp)
		exp = getBreakExp(extra);
	return <\for(init, cond, updaters, body)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//for(list[Expression] initializers, list[Expression] updaters, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\for(initializers, updaters, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	init = for(i <- init){
		<temp, exp, replacementVariables, replacementIds> = inlineLocal(i, local, exp, replacementVariables, replacementIds, synchronizedMethods);
		if(!isLocalAssignment(i, local))
			append(temp);
	}
	<body, exp, replacementVariables, replacementIds> = inlineLocal(body, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	updaters = for(u <- updaters){
		<temp, exp, replacementVariables, replacementIds> = inlineLocal(u, local, exp, replacementVariables, replacementIds, synchronizedMethods);
		if(!isLocalAssignment(u, local))
			append(temp);
	}
	return <\for(init, updaters, body)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//if(Expression condition, Statement thenB)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\if(cond, thenB), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	<thenB, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(thenB, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	return <\if(cond, thenB)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\if(cond, thenB, elseB), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	<thenB, thenExp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(thenB, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	<elseB, elseExp, replacementVariables, replacementIds, extraElse> = inlineLocalInStatement(elseB, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	extra = updateExtra(extra, extraElse);
	if(Expression::null() := thenExp)
		exp = elseExp;
	else
		exp = thenExp; 
	return <\if(cond, thenB, elseB)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//label(str name, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:label(_,_), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	assert false: "Labeled block";
	return <s, exp, replacementVariables, replacementIds, extra>;
}

//return(Expression expression)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\return(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<e, exp, replacementVariables, replacementIds> = inlineLocal(e, exp, replacementVariables, replacementIds, synchronizedMethods);
	return <\return(e)[@src = s@src], Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), exp, ())>;
}

//return()
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\return(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), exp, ())>;

//switch(Expression exp, list[Statement] statements)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\switch(e, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<e, replacementVariables, replacementIds> = inlineLocal(e, exp, replacementVariables, replacementIds, synchronizedMethods);
	cexp = exp;
	HelpingExp extra;
	body = for(stmt <- body){
		switch(stmt){
			case \case(_):{
				cexp = exp;
			}
			case  \defaultCase():{
				hasDefault = true;
				cexp = exp;
			}
			default:{
				<stmt, cexp, replacementVariables, replacementIds, extraC> = inlineLocalInStatement(stmt, cexp, replacementVariables, replacementIds, synchronizedMethods);
				extra = updateExtra(extra, extraC);
			}
		}
		append(stmt);
	}
	if(hasDefault)
		exp = cexp;
	return <\switch(e, body)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//synchronizedStatement(Expression lock, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:synchronizedStatement(l, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	<l, exp, replacementVariables, replacementIds> = inlineLocal(l, exp, replacementVariables, replacementIds, synchronizedMethods);
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, exp, replacementVariables, replacementIds, synchronizedMethods);
	return <synchronizedStatement(l, body)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//throw(Expression exp)
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\throw(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, set[loc] synchronizedMethods){
	exs = ();
	exs[extractClassName(e@decl)] =  exp;
	return <s, exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), Expression::null(), exs)>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\try(body, catchStatements), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	<body, exp, replacementVariables, replacementIds, inlinedBy, extra> = inlineLocalInStatement(body, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	exitExtra = ();
	catchStatements = for(cs <- catchStatements){
		<cs, expC, replacementVariables, replacementIds, inlinedBy, extraC> = gatherStmtFromCatchStatements(cs, exp, replacementVariables, replacementIds, synchronizedMethods, inlinedBy, getExceptionExp(extra));	
		exitExtra = updateExtra(exitExtra, extraC);
		append(cs);
	}
	return <\try(body, catchStatements)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, exitExtra>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally) 
tuple[Statement, Expression, set[loc], map[loc,loc], HelpingExp] inlineLocalInStatement(Statement s:\try(body, catchStatements, fin), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	<body, exp, replacementVariables, replacementIds, inlinedBy, extra> = inlineLocalInStatement(body, local, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	exitExtra = helpingExp(Expression::null(),Expression::null(),Expression::null(),());
	catchStatements = for(cs <- catchStatements){
		<cs, expC, replacementVariables, replacementIds, inlinedBy, extraC> = inlineLocalInStatement(cs, local, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods, getExceptionExp(extra));	
		exitExtra = updateExtra(exitExtra, extraC);
		append(cs);
	}
	if(Expression::null() := exp){
		exp = getBreakExp(extra);
	}
	if(Expression::null() := exp){
		exp = getContinueExp(extra);
	}
	if(Expression::null() := exp){
		exp = getReturnExp(extra);
	}
	<fin, exp, replacementVariables, replacementIds, extraC> = inlineLocalInStatement(fin, local, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);	
	exitExtra = updateExtra(exitExtra, extraC);
	return <\try(body, catchStatements, fin)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, exitExtra>;
}

//\catch(Declaration exception, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\catch(except, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods, map[str, Expression] extra){
	HelpingExp newExtra = helpingExp(Expression::null(), Expression::null(), Expression::null(), ());
	visit(except){
		case e:simpleName(_) : {
			<exceptionExp, extra> = getAndRemoveExp(extra, e@decl.path);
			<body, exp, replacementVariables, replacementIds, extraC> = inlineLocalInStatement(body, local, exceptionExp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);	
			newExtra = updateExtra(newExtra, extraC);
		}
	}
	return <\catch(except, body)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, updateExtra(newExtra, helpingExp(Expression::null(), Expression::null(), Expression::null(), extra))>;
}

//\declarationStatement(Declaration declaration)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:declarationStatement(v:variables(t, frags)), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	frags = for(f <- frags){
		if(f@decl == local){
			exp = getInitFromVariable(f);
			if(containsSynchronizedMethodCalls(exp, synchronizedMethods))
				throw "Inlined expression contains synchronized method calls, <exp@src>";
					
			replacementVariables = collectVariables(exp, replacementVariables);
			println("Local variable found at <f@src>!");
		}
		else{
			<f, exp, replacementVariables, replacementIds> = inlineLocal(f, local, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
			append(f);
		}
	}
	extra = helpingExp(Expression::null(), Expression::null(), Expression::null(), ());
	if(frags == [])
		return <Statement::empty()[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, extra>;
	else{
		return <declarationStatement(variables(t, frags))[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, extra>;
	}
}
//\while(Expression condition, Statement body)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]],HelpingExp] inlineLocalInStatement(Statement s:\while(cond, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	<cond, exp, replacementVariables, replacementIds, inlinedBy> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	<body, exp, replacementVariables, replacementIds, inlinedBy, extra> = inlineLocalInStatement(body, local, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	
	if(Expression::null() := exp)
		exp = getBreakExp(extra);
	
	return <\while(cond, body)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//expressionStatement(Expression stmt)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\expressionStatement(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	<temp, exp, replacementVariables, replacementIds, inlinedBy> = inlineLocal(e, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	if(isLocalAssignment(e, local))
		return <Statement::empty()[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
	else
		return <expressionStatement(temp)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
}


//\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:constructorCall(isSuper, e, args), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods) {
	 <e, exp, replacementVariables, replacementIds, inlinedBy> = inlineLocal(e, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	 args = for(arg <- args){
	 	<arg, exp, replacementVariables, replacementIds, inlinedBy> = inlineLocal(arg, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	 	append(arg);
	 }
	 return <constructorCall(isSuper, e, args)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
}
 //\constructorCall(bool isSuper, list[Expression] arguments)
tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:constructorCall(isSuper, args), loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods) {
	 args = for(arg <- args){
	 	<arg, exp, replacementVariables, replacementIds, inlinedBy> = inlineLocal(arg, exp, replacementVariables, replacementIds, inlinedBy, synchronizedMethods);
	 	append(arg);
	 }
	 return <constructorCall(isSuper, args)[@src = s@src], exp, replacementVariables, replacementIds, inlinedBy, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
}

default tuple[Statement, Expression, set[loc], map[loc,loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s, loc local, Expression exp, set[loc] replacementVariables, map[loc,loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods)
	= <s, exp, replacementVariables, replacementIds, inlinedBy, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;

bool breakingControlFlow(Statement s:\continue()) = true;
bool breakingControlFlow(Statement s:\break()) = true;
bool breakingControlFlow(Statement s:\break("")) = true;
bool breakingControlFlow(Statement s:\return()) = true;
bool breakingControlFlow(Statement s:\return(_)) = true;
bool breakingControlFlow(Statement s:\throw(_)) = true;
default bool breakingControlFlow(Statement s) =  false;
	
tuple[Expression, Expression, set[loc], map[loc,loc], map[loc,set[loc]]] inlineLocal(Expression b, loc local, Expression exp, set[loc] replacementVariables, map[loc, loc] replacementIds, map[loc,set[loc]] inlinedBy, set[loc] synchronizedMethods){
	b = top-down-break visit(b){
		case e:conditional(cond, ifE, elseE):{
			<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			<ifE, exp, replacementVariables, replacementIds> = inlineLocal(ifE, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			<elseE, exp, replacementVariables, replacementIds> = inlineLocal(elseE, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			insert conditional(cond, ifE, elseE)[@src = e@src][@typ = e@typ];
		}
		case e:postfix(operand, operator):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				exp = infix(exp, substring(operator, 1), number("1")[@typ = TypeSymbol::\int()][@src = e@src], [])[@typ = exp@typ][@src = e@src];
				insert(exp);
			}
			else{
				fail;
			}
		}
		case e:prefix(operator, operand):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				exp = infix(exp, substring(operator, 1), number("1")[@typ = TypeSymbol::\int()][@src = e@src], [])[@typ = exp@typ][@src = e@src];
				insert(exp);
			}
			else{
				fail;
			}
		}
		case e: assignment(lhs, operator, rhs):{
			<temp, exp, replacementVariables, replacementIds> = inlineLocal(rhs, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			if(!isArrayAccess(lhs) && lhs@decl == local){
				if(containsSynchronizedMethodCalls(temp, synchronizedMethods)){
					throw "Inlined expression contains synchronized method calls <rhs@src>";
				}
				replacementVariables = collectVariables(temp, replacementVariables);
				if(operator == "="){
					exp = temp;
					insert temp;
				}
				else{
					exp = infix(exp, substring(operator,0,1), temp, [])[@typ = e@typ][@src = e@src];
					insert exp;
				}					
			}
			else
				fail;
		}
		case e:simpleName(_):{
			if(e@decl == local){
				temp = addGeneratedId(exp);
				replacementIds = mapOriginalIdsWithInlined(temp, replacementIds);
				inlinedBy[e@src] = gatherNewIds(temp);
				insert temp;
			}
			else{
				fail;
			}
		}
	}
	return <b, exp, replacementVariables, replacementIds, inlinedBy>;
}

map[loc, loc] mapOriginalIdsWithInlined(temp, map[loc, loc] replacementIds){
	visit(temp){
		case Expression e:{
			replacementIds[e@src] = e@oldSrc;
		}
	}
	return replacementIds;
}

set[loc] gatherNewIds(Expression temp)
	= {e@src | /Expression e <- temp};

bool containsSynchronizedMethodCalls(Expression exp, set[loc] synchronizedMethods){
	visit(exp){
		case c:methodCall(_, _, _):{
			if(c@decl in synchronizedMethods)
				return true;
		}
		case c:methodCall(_,_, _, _):{
			if(c@decl in synchronizedMethods)
				return true;
		}
	}
	return false;
}

HelpingExp updateExtra(HelpingExp e1:helpingExp(c1, b1, r1, exs1), HelpingExp e2:helpingExp(c2, b2, r2, exs2)){
	if(Expression::null() := c1)
		c1 = c2;
	if(Expression::null() := b1)
		b1 = b2;
	if(Expression::null() := r1)
		r1 = r2; 
	return helpingExp(c1, b1, r1, exs1 + exs2);
}

tuple[Expression, map[str, Expression]] getAndRemoveExp(map[str, Expression] exs, str name)
	= <exs[name] ? Expression::null(), delete(exs, name)>;


Expression getContinueExp(HelpingExp e:helpingExp(c, b, r, exs)) = c;

Expression getBreakExp(HelpingExp e:helpingExp(c, b, r, exs)) = b;

Expression getReturnExp(HelpingExp e:helpingExp(c, b, r, exs)) = r;

map[str, Expression] getExceptionExp(HelpingExp e:helpingExp(c, b, r, exs)) = exs;