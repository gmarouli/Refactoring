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
import refactoring::rearranging_code::GenerateIds;


set[Declaration] inlineLocal(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	
	p = createDFG(asts);
	synchronizedMethods = getSynchronizedMethods(p, getCallGraph(asts));
	
	map[loc, set[loc]] replacementIds = ();
	refactoredAsts = visit(asts){
		case m:method(r, n, ps, exs, b):{
			if(m@decl == targetedMethodDecl){
				<b, successful, _, _, vs, replacementIds> = inlineLocal(b, local, false, false, Expression::null(), {}, replacementIds, synchronizedMethods);
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
	
	pR = createDFG(refactoredAsts);
		
	if(checkInlineLocal(p,pR, local, replacementIds)){
		println("Refactoring InlineLocal successful!");
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
	
tuple[Statement, bool, bool, Expression, set[loc], map[loc, set[loc]]] inlineLocal(Statement blockStmt, loc local, bool successful, bool replaceOn, Expression exp, set[loc] replacementVariables, map[loc,set[loc]] replacementIds, set[loc] synchronizedMethods){
	nreplaceOn = replaceOn;
	blockStmt = top-down-break visit(blockStmt){
		case s:block(stmts):{
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables, replacementIds> = inlineLocal(stmt, local, successful, nreplaceOn, exp, replacementVariables, replacementIds, synchronizedMethods);
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
			if(frags == [])
				insert Statement::empty();
			else{
				insert declarationStatement(variables(t, frags))[@src = s@src];
			}
		}
		case s:expressionStatement(e):{
			if(nreplaceOn){
				<temp, exp, replacementVariables, replacementIds> = inlineLocal(e, local, exp, replacementVariables, replacementIds, synchronizedMethods);
				if(isLocalAssignment(e, local))
					insert Statement::empty();
				else
					insert expressionStatement(temp)[@src = s@src];
			}
			else
				fail;
		}
		case Expression e:{
			if(nreplaceOn){
				<e, exp, replacementVariables, replacementIds> = inlineLocal(e, local, exp, replacementVariables, replacementIds, synchronizedMethods);
				insert e;
			}
			else
				fail;
		}
	}
	return <blockStmt, successful, nreplaceOn, exp, replacementVariables, replacementIds>;
}

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