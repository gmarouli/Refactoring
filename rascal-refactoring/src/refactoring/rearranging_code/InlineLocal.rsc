module refactoring::rearranging_code::InlineLocal

import IO;
import Set;
import String;

import PrettyPrint;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::Java2SDFG;
import lang::sccfg::converter::util::Getters;

import refactoring::microrefactorings::GetInfo;
import refactoring::microrefactorings::MicroRefactorings;
import refactoring::rearranging_code::GenerateIds;

data HelpingExp = helpingExp(Expression contExp, Expression brExp, Expression retExp, map[str, Expression] exs);

set[Declaration] inlineLocal(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	
	//Collect synchronized methods
	p = createDFG(asts);
	synchronizedMethods = getSynchronizedMethods(p, getCallGraph(asts));
	
	map[loc, set[loc]] replacementIds = ();
	
	refactoredAsts = visit(asts){
		case m:method(r, n, ps, exs, b):{
			if(m@decl == targetedMethodDecl){
				insert method(r, n, ps, exs, inlineLocal(b, local, {}, replacementIds, synchronizedMethods))[@src = m@src][@decl = m@decl][@typ = m@typ];
			}
			else
				fail;
		}
	}
	
	pR = createDFG(refactoredAsts);
		
	//if(checkInlineLocal(p,pR, local, replacementIds)){
	//	println("Refactoring InlineLocal successful!");
		return refactoredAsts;
	//}
	//else{
	//	println("Refactoring failed!");
	//	return asts;
	//}
}

bool checkInlineLocal(Program original, Program refactored, loc local, map[loc, set[loc]] replacementIds){
	if(!allAssignsToLocalRemoved(refactored, local)){
		println("Error: assigns to the local variable are not removed!");
		return false;
	}
	
	if(!preserveGraphFlow(original, refactored, local, replacementIds)){
		println("Error: data flow is not preserved!");
		return false;
	}
	return true;
}

bool allAssignsToLocalRemoved(Program p, loc local){
	for(assign(_, var, _) <- p.statements){
		if(var == local)
			return false;
	}
	return true;
}

bool preserveGraphFlow(Program original, Program refactored, loc local, map[loc, set[loc]] replacementIds){
	
	//create maps to speed up the look up
	map[loc, Stmt] originalStmts = (getIdFromStmt(stmt) : stmt | stmt <- original.statements);
	map[loc, Stmt] refactoredStmts = (getIdFromStmt(stmt) : stmt | stmt <- refactored.statements);
	
	//Get the changed stmts
	changes = {stmt | stmt <- original.statements} - { stmt | stmt <- refactored.statements};
	refactoredAdditions =  { stmt | stmt <- refactored.statements} - {stmt | stmt <- original.statements};
	
	for(stmt <- changes){
		if(getVarFromStmt(stmt) == local)
			continue;
		//if the changed stmt is not one of the inlined expressions
		if(!(getIdFromStmt(stmt) in replacementIds)){
			//and the original did not refer to the local variable:
			if(getVarFromStmt(originalStmts[getDependencyFromStmt(stmt)]) != local){
				println("Error: the dependency of <stmt> changed to <refactoredStmts[getIdFromStmt(stmt)]>!");
				return false;
			}
		}
		else{
			//sameIds = -1 : unknown, 0 : no, 1 : yes
			int sameIds = -1;  
			//check that all the refactored stmts refer to either to the same id or the refactored one
			for(refactoredId <- replacementIds[getIdFromStmt(stmt)]){
				//if the dependency of the ids are the same
				refactoredStmt = refactoredStmts[refactoredId];
				if(getDependencyFromStmt(refactoredStmt) == getDependencyFromStmt(stmt)){
					if(sameIds == 0){
						println("Error: <stmt> does not have consistent dependencies!");
						return false;
					}
					else{
						sameIds = 1;
					}
				}
				//if the dependency id is not the same 
				else{
					if(sameIds == 1){
						println("Error: <stmt> does not have consistent dependencies!");
						return false;
					}
					else{
						//check if it refers to the replace one
						if(!(getDependencyFromStmt(refactoredStmt) in (replacementIds[getDependencyFromStmt(stmt)] ? {}))){
							println("Error: <stmt> does not have consistent dependencies!");
							return false;
						}
						sameIds = 0;					
					}
				}
			}
		}
	}	
	return true;
}

bool isAssign(Stmt e:assign(_,_,_))
	= true;
default bool isAssign(Stmt e)
	= false;
	
Statement inlineLocal(Statement blockStmt, loc local, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	loc targetBlock = findBlockContainingLocal(blockStmt, local);
	return top-down-break visit(blockStmt){
		case s:block(stmts):{
			if(s@src == targetBlock){
				stmts = for(stmt <- stmts){
					<stmt, exp, replacementVariables, replacementIds, _> = inlineLocalInStatement(stmt, local, Expression::null(), replacementVariables, replacementIds, synchronizedMethods);
					append(stmt);
				}
				if(containsFieldsOrMethods(replacementVariables))
					println("Warning: this refactoring inlined code that contained shared variables (fields) or method calls. In concurrent execution the value assigned from inlining could be different.");
				insert block(stmts)[@src = s@src];
			}
			else
				fail;
		}
	}
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
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:block(sB), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
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
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\break(), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), exp, Expression::null(), ())>;

//break("")
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\break(""), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), exp, Expression::null(), ())>;

//break(str label)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\break(exp), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	if(exp == "")
		fail;
	assert false : "Labeled statement (break) found!!!";
	return <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), exp, Expression::null(), ())>;
}

//continue()
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\continue(), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(exp, Expression::null(), Expression::null(), ())>;
	
//continue(str label)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\continue(exp), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	assert false : "Labeled statement (continue) found!!!";
	return <s, Expression::null(), replacementVariables, replacementIds, helpingExp(exp, Expression::null(), Expression::null(), ())>;
}

//do(Statement body, Expression condition)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\do(b, cond), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
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
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\foreach(parameter, collection, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<collection, exp, replacementVariables, replacementIds, extra> = inlineLocal(collection, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	if(Expression::null() := exp){
		exp = getBreakExp(extra);
	}	
	return <\foreach(parameter, collection, body)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\for(init, cond, updaters, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
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
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\for(initializers, updaters, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
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
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\if(cond, thenB), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	<thenB, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(thenB, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	return <\if(cond, thenB)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\if(cond, thenB, elseB), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	<thenB, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(thenB, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	<elseB, exp, replacementVariables, replacementIds, extraElse> = inlineLocalInStatement(elseB, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	extra = updateExtra(extra, extraElse);
	return <\if(cond, thenB, elseB)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//label(str name, Statement body)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:label(_,_), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	assert false: "Labeled block";
	return <s, exp, replacementVariables, replacementIds, extra>;
}

//return(Expression expression)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\return(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<e, exp, replacementVariables, replacementIds> = inlineLocal(e, exp, replacementVariables, replacementIds, synchronizedMethods);
	return <\return(e)[@src = s@src], Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), exp, ())>;
}

//return()
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\return(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods)
	= <s, Expression::null(), replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), exp, ())>;

//switch(Expression exp, list[Statement] statements)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\switch(e, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
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
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:synchronizedStatement(l, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<l, exp, replacementVariables, replacementIds> = inlineLocal(l, exp, replacementVariables, replacementIds, synchronizedMethods);
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, exp, replacementVariables, replacementIds, synchronizedMethods);
	return <synchronizedStatement(l, body)[@src = s@src], exp, replacementVariables, replacementIds, extra>;
}

//throw(Expression exp)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\throw(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	exs[extractClassName(exp@decl)] =  exp;
	return <s, exp, replacementVariables, replacementIds, helpingExtra(Expression::null(), Expression::null(), Expression::null(), exs)>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\try(body, catchStatements), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, exp, replacementVariables, replacementIds, synchronizedMethods);
	exitExtra = ();
	catchStatements = for(cs <- catchStatements){
		<cs, expC, replacementVariables, replacementIds, extraC> = gatherStmtFromCatchStatements(cs, exp, replacementVariables, replacementIds, synchronizedMethods, extra);	
		exitExtra = updateExtra(exitExtra, extraC);
		append(cs);
	}
	return <\try(body, catchStatements)[@src = s@src], exp, replacementVariables, replacementIds, exitExtra>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally) 
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\try(body, catchStatements, fin), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocalInStatement(body, exp, replacementVariables, replacementIds, synchronizedMethods);
	exitExtra = ();
	catchStatements = for(cs <- catchStatements){
		<cs, expC, replacementVariables, replacementIds, extraC> = inlineLocalInStatement(cs, exp, replacementVariables, replacementIds, synchronizedMethods, extra);	
		exitExtra = updateExtra(exitExtra, extraC);
		append(cs);
	}
	<fin, exp, replacementVariables, replacementIds, extraC> = inlineLocalInStatement(cs, exp, replacementVariables, replacementIds, synchronizedMethods);	
	exitExtra = updateExtra(exitExtra, extraC);
	return <\try(body, catchStatements, fin)[@src = s@src], exp, replacementVariables, replacementIds, exitExtra>;
}

//\catch(Declaration exception, Statement body)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\catch(except, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	HelpingExp extra;
	visit(except){
		case e:simpleName(_) : {
			<exceptionExp, extra> = getAndRemoveExp(extra, e@decl.path);
			<body, exp, replacementVariables, replacementIds, extraC> = inlineLocalInStatement(body, local, exceptionExp, replacementVariables, replacementIds, synchronizedMethods);	
			extra = updateExtra(extra, extraC);
		}
	}
	return <\catch(except, body)[@src = s@src], exp, replacementVariables, replacementIds, extraC>;
}

//\declarationStatement(Declaration declaration)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:declarationStatement(v:variables(t, frags)), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	frags = for(f <- frags){
		if(f@decl == local){
			exp = getInitFromVariable(f);
			if(containsSynchronizedMethodCalls(exp, synchronizedMethods))
				throw "Inlined expression contains synchronized method calls, <exp@src>";
					
			replacementVariables = collectVariables(exp, replacementVariables);
			println("Local variable found at <f@src>!");
		}
		else{
			<f, exp, replacementVariables, replacementIds> = inlineLocal(f, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			append(f);
		}
	}
	extra = helpingExp(Expression::null(), Expression::null(), Expression::null(), ());
	if(frags == [])
		return <Statement::empty()[@src = s@src], exp, replacementVariables, replacementIds, extra>;
	else{
		return <declarationStatement(variables(t, frags))[@src = s@src], exp, replacementVariables, replacementIds, extra>;
	}
}
//\while(Expression condition, Statement body)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\while(cond, body), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	<body, exp, replacementVariables, replacementIds, extra> = inlineLocal(body, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	
	if(Expression::null() := exp)
		exp = getBreakExp(extra);
	
	return <\while(cond, body)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), getReturnExp(extra), getExceptionExp(extra))>;
}

//expressionStatement(Expression stmt)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:\expressionStatement(e), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	<temp, exp, replacementVariables, replacementIds> = inlineLocal(e, local, exp, replacementVariables, replacementIds, synchronizedMethods);
	if(isLocalAssignment(e, local))
		return <Statement::empty()[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
	else
		return <expressionStatement(temp)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
}


//\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:constructorCall(isSuper, e, args), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods) {
	 <e, exp, replacementVariables, replacementIds> = inlineLocal(e, exp, replacementVariables, replacementIds, synchronizedMethods);
	 args = for(arg <- args){
	 	<arg, exp, replacementVariables, replacementIds> = inlineLocal(arg, exp, replacementVariables, replacementIds, synchronizedMethods);
	 	append(arg);
	 }
	 return <constructorCall(isSuper, e, args)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
}
 //\constructorCall(bool isSuper, list[Expression] arguments)
tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s:constructorCall(isSuper, args), loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods) {
	 args = for(arg <- args){
	 	<arg, exp, replacementVariables, replacementIds> = inlineLocal(arg, exp, replacementVariables, replacementIds, synchronizedMethods);
	 	append(arg);
	 }
	 return <constructorCall(isSuper, args)[@src = s@src], exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;
}

default tuple[Statement, Expression, set[loc], map[loc,set[loc]], HelpingExp] inlineLocalInStatement(Statement s, loc local, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods)
	= <s, exp, replacementVariables, replacementIds, helpingExp(Expression::null(), Expression::null(), Expression::null(), ())>;

bool breakingControlFlow(Statement s:\continue()) = true;
bool breakingControlFlow(Statement s:\break()) = true;
bool breakingControlFlow(Statement s:\break("")) = true;
bool breakingControlFlow(Statement s:\return()) = true;
bool breakingControlFlow(Statement s:\return(_)) = true;
bool breakingControlFlow(Statement s:\throw(_)) = true;
default bool breakingControlFlow(Statement s) =  false;
	
tuple[Expression, Expression, set[loc], map[loc,set[loc]]] inlineLocal(Expression b, loc local, Expression exp, set[loc] replacementVariables, map[loc, set[loc]] replacementIds, set[loc] synchronizedMethods){
	b = top-down-break visit(b){
		case e:conditional(cond, ifE, elseE):{
			<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			<ifE, exp, replacementVariables, replacementIds> = inlineLocal(ifE, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			<elseE, exp, replacementVariables, replacementIds> = inlineLocal(elseE, local, exp, replacementVariables, replacementIds, synchronizedMethods);
			insert conditional(cond, ifE, elseE)[@src = e@src][@typ = e@typ];
		}
		case e:postfix(operand, operator):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				exp = infix(exp, substring(operator, 1), number("1")[@typ = TypeSymbol::\int()], [])[@typ = exp@typ][@src = e@src];
				insert(exp);
			}
			else{
				fail;
			}
		}
		case e:prefix(operator, operand):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				exp = infix(exp, substring(operator, 1), number("1")[@typ = TypeSymbol::\int()], [])[@typ = exp@typ][@src = e@src];
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
					insert(temp);
				}
				else{
					exp = infix(exp, substring(operator,0,1), temp, [])[@typ = e@typ][@src = e@src];
					insert(exp);
				}					
			}
			else
				fail;
		}
		case e:simpleName(_):{
			if(e@decl == local){
				temp = addGeneratedId(exp);
				replacementIds = mapOriginalIdsWithInlined(temp, replacementIds);
				insert temp;
			}
			else{
				fail;
			}
		}
	}
	return <b, exp, replacementVariables, replacementIds>;
}

map[loc, set[loc]] mapOriginalIdsWithInlined(temp, map[loc, set[loc]] replacementIds){
	visit(temp){
		case e:simpleName(_):{
			replacementIds[e@oldSrc] = (replacementIds[e@oldSrc] ? {}) + {e@src};
		}
		case e:assignment(_,_,_):{
			replacementIds[e@oldSrc] = (replacementIds[e@oldSrc] ? {}) + {e@src};
		}
		case e:postfix(_,_):{
			replacementIds[e@oldSrc] = (replacementIds[e@oldSrc] ? {}) + {e@src};
		}
		case e:prefix(_,_):{
			replacementIds[e@oldSrc] = (replacementIds[e@oldSrc] ? {}) + {e@src};
		}
	}
	return replacementIds;
}

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

tuple[Expression, map[str, Expression]] getAndRemoveExp(HelpingExp e:helpingExp(c, b, r, exs), str name)
	= <exs[exceptionName] ? Expression::null(), delete(exs, name)>;


Expression getContinueExp(HelpingExp e:helpingExp(c, b, r, exs)) = c;

Expression getBreakExp(HelpingExp e:helpingExp(c, b, r, exs)) = b;

Expression getReturnExp(HelpingExp e:helpingExp(c, b, r, exs)) = r;

map[str, Expression] getExceptionExp(HelpingExp e:helpingExp(c, b, r, exs)) = exs;