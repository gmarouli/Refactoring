module refactoring::rearranging_code::InlineLocal

import IO;
import Set;
import String;

import PrettyPrint;

import lang::java::jdt::m3::AST;

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::Java2DFG;
import lang::sccfg::converter::util::Getters;
import lang::sccfg::converter::util::DataFlowGraph;

import refactoring::microrefactorings::GetInfo;
import refactoring::rearranging_code::GenerateIds;
//import refactoring::microrefactorings::MicroRefactorings;


set[Declaration] inlineLocal(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	map[loc, set[loc]] replacementIds = ();
	refactoredAsts = visit(asts){
		case m:method(r, n, ps, exs, b):{
			if(m@decl == targetedMethodDecl){
				<b, successful, _, _, vs, replacementIds> = inlineLocal(b, local, false, false, false, Expression::null(), {}, replacementIds);
				if(successful)
					println("The refactoring InlineLocal of <local> finished successfully!");
				if(containsFieldsOrMethods(vs))
					println("Warning: this refactoring inlined code that contained shared variables (fields) or method calls. In concurrent execution the value assigned from inlining could be different.");
				insert method(r, n, ps, exs, b)[@src = m@src][@decl = m@decl][@typ = m@typ];
			}
			else
				fail;
		}
	}
	
	<p, g> = createDFG(asts);
	<pR,gR> = createDFG(refactoredAsts);
		
	if(checkInlineLocal(p,pR, local, replacementIds)){
		println("Refactoring InlineLocal successful!");
		prettyPrint(refactoredAsts,"");
		return refactoredAsts;
	}
	else{
		println("Refactoring failed!");
		return asts;
	}
}

bool checkInlineLocal(Program original, Program refactored, loc local, map[loc, set[loc]] replacementIds){
	if(!allAssignsToLocalRemoved(refactored, local)){
		println("Error: assigns to the local variable are not removed!");
		return false;
	}
	
	if(!preserveDataFlow(original, refactored, local, replacementIds)){
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

bool preserveDataFlow(Program original, Program refactored, loc local, map[loc, set[loc]] replacementIds){
	//remove local variable assignments
	//original.statements = {stmt | stmt <- original.statements, getVarFromStmt(stmt) != local};
	
	//create maps to speed up the look up
	map[loc, Stmt] originalStmts = (getIdFromStmt(stmt) : stmt | stmt <- original.statements);
	map[loc, Stmt] refactoredStmts = (getIdFromStmt(stmt) : stmt | stmt <- refactored.statements);
	
	//Get the changed stmts
	changes = {stmt | stmt <- original.statements} - { stmt | stmt <- refactored.statements};
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
	
tuple[Statement, bool, bool, Expression, set[loc], map[loc, set[loc]]] inlineLocal(Statement blockStmt, loc local, bool successful, bool inControlStatement, bool replaceOn, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds){
	nreplaceOn = replaceOn;
	blockStmt = top-down-break visit(blockStmt){
		case s:block(stmts):{
			stmts = for(stmt <- stmts){
				//if the variable is not found yet it does not matter if we are in a control flow environment
				if(!nreplaceOn)
					inControlStatement = false;
				<stmt, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(stmt, local, successful, inControlStatement, nreplaceOn, exp, replacementVariables, replacementIds);
				append(stmt);
			}
			nreplaceOn = replaceOn;
			insert block(stmts)[@src = s@src];
		}
		case s:declarationStatement(v:variables(t, frags)):{
			frags = for(f <- frags){
				if(f@decl == local){
					nreplaceOn = true;
					successful = true;
					exp = getInitFromVariable(f);
					
					replacementVariables = collectVariables(exp, replacementVariables);
					println("Local variable found at <f@src>!");
				}
				else{
					<f, exp, replacementVariables, replacementIds> = inlineLocal(f, local, inControlStatement, exp, replacementVariables, replacementIds);
					append(f);
				}
			}
			if(frags == [])
				insert Statement::empty();
			else{
				insert declarationStatement(variables(t, frags))[@src = s@src];
			}
		}
		case s:expressionStatement(e):{
			if(nreplaceOn){
				<temp, exp, replacementVariables, replacementIds> = inlineLocal(e, local, inControlStatement, exp, replacementVariables, replacementIds);
				if(isLocalAssignment(e, local))
					insert Statement::empty();
				else
					insert expressionStatement(temp)[@src = s@src];
			}
			else
				fail;
		}
		case s:\if(cond, bIf, bElse):{
			if(nreplaceOn)
				<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables, replacementIds);
			<bIf, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(bIf, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			<bElse, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(bElse, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			insert \if(cond, bIf, bElse)[@src = s@src];
		}
		case s:\if(cond, b):{
			if(nreplaceOn)
				<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables, replacementIds);
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			insert \if(cond, b)[@src = s@src];
		}
		case s:\while(cond, b):{
			if(nreplaceOn)
				<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, true, exp, replacementVariables, replacementIds);
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			insert \while(cond, b)[@src = s@src];
		}
		case s:\do(b, cond):{
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			if(nreplaceOn)
				<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, true, exp, replacementVariables, replacementIds);
			insert \do(b, cond)[@src = s@src];
		}
		case s:\foreach(p, col, b):{
			if(nreplaceOn)
				<col, exp, replacementVariables, replacementIds> = inlineLocal(col, local, true, exp, replacementVariables, replacementIds);
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			insert \foreach(p, col, b)[@src = s@src];
		}
		case s:\for(init, cond, updaters, b):{
			if(nreplaceOn){
				init = for(i <- init){
					<i, exp, replacementVariables, replacementIds> = inlineLocal(i, local, true, exp, replacementVariables, replacementIds);
					append(i);
				}
				<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, true, exp, replacementVariables, replacementIds);
			}
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			if(nreplaceOn){
				updaters = for(u <- updaters){
					<u, exp, replacementVariables, replacementIds> = inlineLocal(u, local, true, exp, replacementVariables, replacementIds);
					append(u);
				}
			}
			insert \for(init, cond, updaters, b)[@src = s@src];
		}
		case s:\for(init, updaters, b):{
			if(nreplaceOn){
				init = for(i <- init){
					<i, exp, replacementVariables, replacementIds> = inlineLocal(i, local, true, exp, replacementVariables, replacementIds);
					append(i);
				}
			}
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			if(nreplaceOn){
				updaters = for(u <- updaters){
					<u, exp, replacementVariables, replacementIds> = inlineLocal(u, local, true, exp, replacementVariables, replacementIds);
					append(u);
				}
			}
			insert \for(init, cond, updaters, b)[@src = s@src];
		}
		case s:\switch(cond, stmts):{
			if(nreplaceOn){
				<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables, replacementIds);
			}
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(stmt, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
				append(stmt);
			}
			insert \switch(cond, stmts)[@src = s@src];
		}
		case s:\try(b, stmts):{
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(stmt, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
				append(stmt);
			}
			insert \try(b, stmts)[@src = s@src];
		}
		case s:\try(b, stmts, fin):{
			<b, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(stmt, local, successful, true, nreplaceOn, exp, replacementVariables, replacementIds);
				append(stmt);
			}
			<fin, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(fin, local, successful, inControlStatement, nreplaceOn, exp, replacementVariables, replacementIds);
			insert \try(b, stmts, fin)[@src = s@src];
		}
		case Expression e:{
			if(nreplaceOn){
				<e, exp, replacementVariables, replacementIds> = inlineLocal(e, local, true, exp, replacementVariables, replacementIds);
				insert e;
			}
			else
				fail;
		}
	}
	return <blockStmt, successful, nreplaceOn, exp, replacementVariables, replacementIds>;
}

tuple[Expression, Expression, set[loc], map[loc,set[loc]]] inlineLocal(Expression b, loc local, bool inControlStatement, Expression exp, set[loc] replacementVariables, map[loc, set[loc]] replacementIds){
	b = top-down-break visit(b){
		case e:infix(lhs, operator, rhs, exts):{
			if((operator == "&&") || (operator == "||")){
				<lhs, exp, replacementVariables, replacementIds> = inlineLocal(lhs, local, inControlStatement, exp, replacementVariables, replacementIds);
				<rhs, exp, replacementVariables, replacementIds> = inlineLocal(lhs, local, true, exp, replacementVariables, replacementIds);
				exts = for(ext <- exts){
					<ext, exp, replacementVariables, replacementIds> = inlineLocal(ext, local, true, exp, replacementVariables, replacementIds);
					append(ext);
				}
				insert infix(lhs, operator, rhs, exts)[@src = e@src][@typ = e@typ];
			}
			else
				fail;
		}
		case e:conditional(cond, ifE, elseE):{
			<cond, exp, replacementVariables, replacementIds> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables, replacementIds);
			<ifE, exp, replacementVariables, replacementIds> = inlineLocal(ifE, local, true, exp, replacementVariables, replacementIds);
			<elseE, exp, replacementVariables, replacementIds> = inlineLocal(elseE, local, true, exp, replacementVariables, replacementIds);
			insert conditional(cond, ifE, elseE)[@src = e@src][@typ = e@typ];
		}
		case e:postfix(operand, operator):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				if(inControlStatement){
					throw "Failed refactoring: Assignment to the local variable in control statement. <e@src>";
				}
				else{
					exp = infix(exp, substring(operator, 1), number("1")[@typ = TypeSymbol::\int()], [])[@typ = exp@typ][@src = e@src];
					insert(exp);
				}
			}
			else{
				fail;
			}
		}
		case e:prefix(operator, operand):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				if(inControlStatement){
					throw "Failed refactoring: Assignment to the local variable in control statement.";
				}
				else{
					exp = infix(exp, substring(operator, 1), number("1")[@typ = TypeSymbol::\int()], [])[@typ = exp@typ][@src = e@src];
					insert(exp);
				}
			}
			else{
				fail;
			}
		}
		case e: assignment(lhs, operator, rhs):{
			<temp, exp, replacementVariables, replacementIds> = inlineLocal(rhs, local, inControlStatement, exp, replacementVariables, replacementIds);
			if(lhs@decl == local){
				if (inControlStatement){
					throw "Failed refactoring: Assignment to the local variable in control statement. <e@src>";
				}
				
				replacementVariables = collectVariables(temp, replacementVariables);
				if(operator == "="){
					exp = temp;
					insert(temp);
				}
				if(operator == "+="){
					exp = infix(exp, "+", temp, [])[@typ = e@typ][@src = e@src];
					insert(exp);
				}
				if(operator == "-="){
					exp = infix(exp, "-", temp, [])[@typ = e@typ][@src = e@src];
					insert(exp);
				}					
			}
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