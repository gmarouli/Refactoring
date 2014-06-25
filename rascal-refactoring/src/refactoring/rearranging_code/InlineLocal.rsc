module refactoring::rearranging_code::InlineLocal

import IO;
import String;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;
import refactoring::microrefactorings::GetInfo;

set[Declaration] inlineLocal(set[Declaration] asts, loc local){
	targetedMethodDecl = getMethodDeclFromVariable(local);
	return visit(asts){
		case m:method(r, n, ps, exs, b):{
			if(m@decl == targetedMethodDecl){
				<b, successful, _, _, vs> = inlineLocal(b, local, false, false, false, Expression::null(), {});
				if(successful)
					println("The refactoring InlineLocal of <local> finished successfully!");
				if(containsFields(vs))
					println("Warning: this refactoring moved code that contained shared variables (fields). In concurrent execution the value assigned from inlining could be different.");
				insert method(r, n, ps, exs, b)[@src = m@src][@decl = m@decl][@typ = m@typ];
			}
			else
				fail;
		}
	}
}
	
tuple[Statement, bool, bool, Expression, set[loc]] inlineLocal(Statement blockStmt, loc local, bool successful, bool inControlStatement, bool replaceOn, Expression exp, set[loc] replacementVariables){
	nreplaceOn = replaceOn;
	blockStmt = top-down-break visit(blockStmt){
		case s:block(stmts):{
			stmts = for(stmt <- stmts){
				//if the variable is not found yet it does not matter if we are in a control flow environment
				if(!nreplaceOn)
					inControlStatement = false;
				<stmt, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(stmt, local, successful, inControlStatement, nreplaceOn, exp, replacementVariables);
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
					<f, exp, replacementVariables> = inlineLocal(f, local, inControlStatement, exp, replacementVariables);
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
				<temp, exp, replacementVariables> = inlineLocal(e, local, inControlStatement, exp, replacementVariables);
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
				<cond, exp, replacementVariables> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables);
			<bIf, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(bIf, local, successful, true, nreplaceOn, exp, replacementVariables);
			<bElse, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(bElse, local, successful, true, nreplaceOn, exp, replacementVariables);
			insert \if(cond, bIf, bElse)[@src = s@src];
		}
		case s:\if(cond, b):{
			if(nreplaceOn)
				<cond, exp, replacementVariables> = inlineLocal(cond, local, successfull,inControlStatement, exp, replacementVariables);
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			insert \if(cond, b)[@src = s@src];
		}
		case s:\while(cond, b):{
			if(nreplaceOn)
				<cond, exp, replacementVariables> = inlineLocal(cond, local, true, exp, replacementVariables);
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			insert \while(cond, b)[@src = s@src];
		}
		case s:\do(b, cond):{
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			if(nreplaceOn)
				<cond, exp, replacementVariables> = inlineLocal(cond, local, true, exp, replacementVariables);
			insert \do(b, cond)[@src = s@src];
		}
		case s:\foreach(p, col, b):{
			if(nreplaceOn)
				<col, exp, replacementVariables> = inlineLocal(col, local, true, exp, replacementVariables);
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			insert \foreach(p, col, b)[@src = s@src];
		}
		case s:\for(init, cond, updaters, b):{
			if(nreplaceOn){
				init = for(i <- init){
					<i, exp, replacementVariables> = inlineLocal(i, local, true, exp, replacementVariables);
					append(i);
				}
				<cond, exp, replacementVariables> = inlineLocal(cond, local, true, exp, replacementVariables);
			}
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			if(nreplaceOn){
				updaters = for(u <- updaters){
					<u, exp, replacementVariables> = inlineLocal(u, local, true, exp, replacementVariables);
					append(u);
				}
			}
			insert \for(init, cond, updaters, b)[@src = s@src];
		}
		case s:\for(init, updaters, b):{
			if(nreplaceOn){
				init = for(i <- init){
					<i, exp, replacementVariables> = inlineLocal(i, local, true, exp, replacementVariables);
					append(i);
				}
			}
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			if(nreplaceOn){
				updaters = for(u <- updaters){
					<u, exp, replacementVariables> = inlineLocal(u, local, true, exp, replacementVariables);
					append(u);
				}
			}
			insert \for(init, cond, updaters, b)[@src = s@src];
		}
		case s:\switch(cond, stmts):{
			if(nreplaceOn){
				<cond, exp, replacementVariables> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables);
			}
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(stmt, local, successful, true, nreplaceOn, exp, replacementVariables);
				append(stmt);
			}
			insert \switch(cond, stmts)[@src = s@src];
		}
		case s:\try(b, stmts):{
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(stmt, local, successful, true, nreplaceOn, exp, replacementVariables);
				append(stmt);
			}
			insert \try(b, stmts)[@src = s@src];
		}
		case s:\try(b, stmts, fin):{
			<b, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(b, local, successful, true, nreplaceOn, exp, replacementVariables);
			stmts = for(stmt <- stmts){
				<stmt, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(stmt, local, successful, true, nreplaceOn, exp, replacementVariables);
				append(stmt);
			}
			<fin, successful, nreplaceOn, exp, replacementVariables> = inlineLocal(fin, local, successful, inControlStatement, nreplaceOn, exp, replacementVariables);
			insert \try(b, stmts, fin)[@src = s@src];
		}
		case Expression e:{
			if(nreplaceOn){
				<e, exp, replacementVariables> = inlineLocal(e, local, true, exp, replacementVariables);
				insert e;
			}
			else
				fail;
		}
	}
	return <blockStmt, successful, nreplaceOn, exp, replacementVariables>;
}

tuple[Expression, Expression, set[loc]] inlineLocal(Expression b, loc local, bool inControlStatement, Expression exp, set[loc] replacementVariables){
	b = top-down-break visit(b){
		case e:infix(lhs, operator, rhs, exts):{
			if((operator == "&&") || (operator == "||")){
				<lhs, exp, replacementVariables> = inlineLocal(lhs, local, inControlStatement, exp, replacementVariables);
				<rhs, exp, replacementVariables> = inlineLocal(lhs, local, true, exp, replacementVariables);
				exts = for(ext <- exts){
					<ext, exp, replacementVariables> = inlineLocal(ext, local, true, exp, replacementVariables);
					append(ext);
				}
				insert infix(lhs, operator, rhs, exts)[@src = e@src][@typ = e@typ];
			}
			else
				fail;
		}
		case e:conditional(cond, ifE, elseE):{
			<cond, exp, replacementVariables> = inlineLocal(cond, local, inControlStatement, exp, replacementVariables);
			<ifE, exp, replacementVariables> = inlineLocal(ifE, local, true, exp, replacementVariables);
			<elseE, exp, replacementVariables> = inlineLocal(elseE, local, true, exp, replacementVariables);
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
			<temp, exp, replacementVariables> = inlineLocal(rhs, local, inControlStatement, exp, replacementVariables);
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
				insert exp;
			}
			else{
				fail;
			}
		}
	}
	return <b, exp, replacementVariables>;
}