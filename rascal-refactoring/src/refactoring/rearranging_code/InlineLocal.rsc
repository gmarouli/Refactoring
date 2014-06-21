module refactoring::rearranging_code::InlineLocal

import lang::java::jdt::m3::AST;
import refactoring::microrefactorings::GetInfo;
import List;
import IO;
import String;
import lang::java::m3::TypeSymbol;

tuple[Statement, bool, Expression] inlineLocal(Statement b, loc local, loc src, bool inControlStatement, bool replaceOn, Expression exp){
	nreplaceOn = replaceOn;
	return <top-down-break visit(b){
		//possibility to contain the declaration
		case s:block(stmts):{
			if((src.offset > s@src.offset) && (src.offset < (s@src.offset + s@src.length))){
				stmts = for(stmt <- stmts){
					<stmt, nreplaceOn, exp> = inlineLocal(stmt, local, src, inControlStatement, nreplaceOn, exp);
					append(stmt);
				}
				nreplaceOn = replaceOn;
				insert block(stmts)[@src = s@src];
			}
			else
				fail;
		}
		case s:declarationStatement(v:variables(t,frags)):{
			if((src.offset > s@src.offset) && (src.offset < (s@src.offset + s@src.length))){
				Expression target;
				for(f <- frags){
					if(f@decl == local){
						target = f;
						nreplaceOn = true;
						exp = getInitFromVariable(f);
						println("Local variable found!");
					}
				}
				if(nreplaceOn){
					if(size(frags) == 1)
						insert Statement::empty();
					else{
						insert declarationStatement(variables(t,delete(frags,target)))[@src = s@src];
					}
				}
			}
			else{
				fail;
			}
		}
		//if the flag replace on is not on just return the statement as it is
		case Statement s:{
			println("In stmt<s>");
			if(!nreplaceOn){
				insert s;
			}
			else{
				fail;
			}
		}
		case s:\if(cond,b):{
			<cond, exp> = inlineLocal(cond, local, inControlStatement, exp);
			println("Call from iff");
			<b, nreplaceOn, exp> = inlineLocal(b, local, src, true, nreplaceOn, exp);
			insert \if(cond, b)[@src = s@src];
		}
		case s:expressionStatement(e):{
			println("<inControlStatement>: In expression stmt <e>");
			<e, exp> = inlineLocal(e, local, inControlStatement, exp);
			if(isInfix(e))
				insert Statement::empty();
			else
				insert expressionStatement(e)[@src = s@src];
		}
		case s:\if(cond,bIf, bElse):{
			<cond, exp> = inlineLocal(cond, local, inControlStatement, exp);
			<bIf, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			<bElse, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			insert \if(cond, bIf, bElse)[@src = s@src];
		}
		case s:\while(cond, b):{
			<cond, exp> = inlineLocal(cond, local, true, exp);
			<b, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			insert \while(cond, b)[@src = s@src];
		}
		case s:\do(b, cond):{
			<b, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			<cond, exp> = inlineLocal(cond, local, true, exp);
			insert \do(b, cond)[@src = s@src];
		}
		case s:\do(b, cond):{
			<b, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			<cond, exp> = inlineLocal(cond, local, true, exp);
			insert \do(b, cond)[@src = s@src];
		}
		case s:\foreach(p, col, b):{
			<col, exp> = inlineLocal(col, local, true, exp);
			<b, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			insert \foreach(p, col, b)[@src = s@src];
		}
		case s:\for(init, cond, updaters, b):{
			init = for(i <- init){
				<i, exp> = inlineLocal(i, local, true, exp);
				append(i);
			}
			<cond, exp> = inlineLocal(cond, local, true, exp);
			<b, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			updaters = for(u <- updaters){
				<u, exp> = inlineLocal(u, local, true, exp);
				append(u);
			}
			insert \for(init, cond, updaters, b)[@src = s@src];
		}
		case s:\for(init, updaters, b):{
			init = for(i <- init){
				<i, exp> = inlineLocal(i, local, true, exp);
				append(i);
			}
			<b, nreplaceOn, exp> = inlineLocal(bIf, local, src, true, nreplaceOn, exp);
			updaters = for(u <- updaters){
				<u, exp> = inlineLocal(u, local, true, exp);
				append(u);
			}
			insert \for(init, cond, updaters, b)[@src = s@src];
		}
		case s:\switch(cond, stmts):{
			<cond, exp> = inlineLocal(cond, local, inControlStatement, exp);
			stmts = for(stmt <- stmts){
				<stmt, nreplaceOn, exp> = inlineLocal(stmt, local, src, true, nreplaceOn, exp);
				append(stmt);
			}
			insert \switch(cond, stmts)[@src = s@src];
		}
		case s:\try(b, stmts):{
			<b, nreplaceOn, exp> = inlineLocal(b, local, src, true, nreplaceOn, exp);
			stmts = for(stmt <- stmts){
				<stmt, nreplaceOn, exp> = inlineLocal(stmt, local, src, true, nreplaceOn, exp);
				append(stmt);
			}
			insert \try(b, stmts)[@src = s@src];
		}
		case s:\try(b, stmts,fin):{
			<b, nreplaceOn, exp> = inlineLocal(b, local, src, true, nreplaceOn, exp);
			stmts = for(stmt <- stmts){
				<stmt, nreplaceOn, exp> = inlineLocal(stmt, local, src, true, nreplaceOn, exp);
				append(stmt);
			}
			<fin, nreplaceOn, exp> = inlineLocal(fin, local, src, inControlStatement, nreplaceOn, exp);
			insert \try(b, stmts,fin)[@src = s@src];
		}
		case Expression e:{
			<e, exp> = inlineLocal(e, local, true, exp);
			insert e;
		}
	}, nreplaceOn, exp>;
}

tuple[Expression, Expression] inlineLocal(Expression b, loc local, bool inControlStatement, Expression exp){
	return <top-down-break visit(b){
		case e:infix(lhs, operator, rhs, exts):{
			if((operator == "&&") || (operator == "||")){
				<lhs, exp> = inlineLocal(lhs, local, inControlStatement, exp);
				<rhs, exp> = inlineLocal(lhs, local, true, exp);
				exts = for(ext <- exts){
					<ext, exp> = inlineLocal(ext, local, true, exp);
					append(ext);
				}
				insert infix(lhs, operator, rhs, exts)[@src = e@src];
			}
			else
				fail;
		}
		case e:conditional(cond, ifE, elseE):{
			<cond, exp> = inlineLocal(cond, local, inControlStatement, exp);
			<ifE, exp> = inlineLocal(ifE, local, true, exp);
			<elseE, exp> = inlineLocal(elseE, local, true, exp);
			insert conditional(cond, ifE, elseE)[@src = e@src];
		}
		case e:postfix(operand, operator):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				if(inControlStatement){
					throw "Failed refactoring: Assignment to the local variable in control statement.";
				}
				else{
					exp = infix(exp,substring(operator,1),number("1")[@typ = TypeSymbol::\int()],[]);
					insert(exp);
				}
			}
			else{
				fail;
			}
		}
		case e:prefix(operator,operand):{
			if(operand@decl == local && ((operator == "++") || (operator == "--"))){
				if(inControlStatement){
					throw "Failed refactoring: Assignment to the local variable in control statement.";
				}
				else{
					exp = infix(exp,substring(operator,1),number("1")[@typ = TypeSymbol::\int()],[]);
					insert(exp);
				}
			}
			else{
				fail;
			}
		}
		case e: assignment(lhs, operator, rhs):{
			<temp, exp> = inlineLocal(rhs, local, inControlStatement, exp);
			if(lhs@decl == local){
				if (inControlStatement){
					throw "Failed refactoring: Assignment to the local variable in control statement.";
				}
				
				if(operator == "="){
					exp = temp;
					insert(temp[@src = e@src]);
				}
				if(operator == "+="){
					exp = infix(exp,"+",temp,[]);
					insert(exp[@src = e@src]);
				}
				if(operator == "-="){
					exp = infix(exp,"-",temp,[]);
					insert(exp[@src = e@src]);
				}					
			}
		}
		case e:simpleName(_):{
			if(e@decl == local){
				insert exp[@src = e@src];
			}
			else{
				fail;
			}
		}
	}, exp>;
}

bool isInfix(Expression e:infix(_,_,_,_)) = true;
default bool isInfix(Expression e) = false;











