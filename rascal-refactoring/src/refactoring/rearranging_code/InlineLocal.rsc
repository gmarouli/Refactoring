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
		case s:block(stmts):{
			stmts = for(stmt <- stmts){
				<nStmt, nreplaceOn, exp> = inlineLocal(stmt, local, src, inControlStatement, nreplaceOn, exp);
				append(nStmt);
			}
			nreplaceOn = replaceOn;
			insert block(stmts)[@src = s@src];
		}
		case s:declarationStatement(v:variables(t,frags)):{
			if((src.offset > s@src.offset) && (src.offset < (s@src.offset + s@src.length))){
				Expression target;
				for(f <- frags){
					if(f@decl == local){
						target = f;
						nreplaceOn = true;
						exp = getInitFromVariable(f);
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
		case e:postfix(operand, operator):{
			println(nreplaceOn);
			if(nreplaceOn){
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
			else
				insert e;
		}
		case e:prefix(operator,operand):{
			if(nreplaceOn){
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
			else
				insert e;
		}
		case e: assignment(lhs, operator, rhs):{
			if(nreplaceOn){
				<expressionStatement(temp), _, exp> = inlineLocal(expressionStatement(rhs),local, src, inControlStatement, nreplaceOn);
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
			else{
				insert e;
			}
		}
		case e:simpleName(_):{
			if(nreplaceOn && (e@decl == local)){
				insert exp[@src = e@src];
			}
			else{
				fail;
			}
		}
	}, nreplaceOn, exp>;
}