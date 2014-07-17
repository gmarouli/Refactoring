module PrettyPrint

import IO;
import String;


import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

loc targetFile = |project://rascal-refactoring/RefactoredCode|;

void prettyPrint(set[Declaration] asts){
	for(a <- asts)
		prettyPrint(a, "");
}

str prettyPrint(list[Declaration] asts, str indent){
	code = "";
	for(a <- asts)
		code += prettyPrint(a, indent);
	return code;
}

//Declarations
void prettyPrint(Declaration c:compilationUnit(imps, typs), str indent){
	targetFile = |project://rascal-refactoring/RefactoredCode|;
	targetFile.path = targetFile.path + c@decl.path;
	println("Creating file: <targetFile>");
	code = prettyPrint(imps, "");
	code += prettyPrint(typs, "");
	writeFile(targetFile,code);
}

void prettyPrint(Declaration c:compilationUnit(package, imps, typs), str indent){
		targetFile = |project://rascal-refactoring/RefactoredCode|;
		targetFile.path = targetFile.path + c@decl.path;
		println("Creating file: <targetFile>");
		code = "package "+prettyPrint(package, "") + ";\n";
		code += prettyPrint(imps, "");
		code += prettyPrint(typs, "");
		writeFile(targetFile,code);
}

str prettyPrint(Declaration c:\class(body), str indent)
	= " {\n" + prettyPrint(body, indent + "\t") + "\n}";

str prettyPrint(Declaration c:\class(name, exts, impls, body), str indent){
	code = indent;
	for(m <- (c@modifiers ? [])){
		code += prettyPrint(m, indent);
		code += " ";
	}
	code += "class " + name;
	if(exts != []){
		code += " extends ";
		for(e <- exts){
			code += prettyPrint(e, indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	if(impls != []){
		code += " implements ";
		for(i <- impls){
			code += prettyPrint(i, indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += " {\n";
	code += prettyPrint(body, indent + "\t");
	code += "\n}";
	return code;
}

str prettyPrint(Declaration f:field(t, frags), str indent){
	code = indent;
	for(m <- (f@modifiers ? [])){
		code += prettyPrint(m, indent);
		code += " ";
	}
	code += prettyPrint(t,indent);
	code += " ";
	for(fr <- frags){
		code += prettyPrint(fr,indent);
		code += ", ";
	}
	code = substring(code, 0, findLast(code, ",")) + ";\n";
	return code;
}

str prettyPrint(Declaration m:method(t, name, ps, exs), indent){
	code = "\n"+indent;
	for(modi <- (m@modifiers ? [])){
		code += prettyPrint(modi, indent);
		code += " ";
	}
	code += prettyPrint(t, indent);
	code += name +"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p, indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ",")) + ")";
	}
	if(exs != []){
		code += " throws ";
		for(e <- exs){
			prettyPrint(e,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + ";\n";
}

str prettyPrint(Declaration m:method(t, name, ps, exs, body), str indent){
	code = "\n" + indent;
	for(modi <- (m@modifiers ? [])){
		code += prettyPrint(modi,indent);
		code += " ";
	}
	code += prettyPrint(t,indent);
	code += " ";
	code += name +"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p, "");
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ") ";
	if(exs != []){
		code += " throws ";
		for(e <- exs){
			prettyPrint(e,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + trim(prettyPrint(body, indent))+"\n";
}

str prettyPrint(Declaration s:constructor(name, ps, exs, body), indent){
	code = "\n" + indent;
	for(modi <- (s@modifiers ? [])){
		code += prettyPrint(modi,indent);
		code += " ";
	}
	code += name +"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p, "");
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ") ";
	if(exs != []){
		code += " throws ";
		for(e <- exs){
			code += prettyPrint(e,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + trim(prettyPrint(body, indent)) + "\n";
}

str prettyPrint(Declaration i:\import(name), str indent)
	= "import " + name + ";\n";

str prettyPrint(Declaration p:package(name), indent)
	= name;
		
str prettyPrint(Declaration p:package(pp, name), indent)
	= prettyPrint(pp, indent) + "." + name;

str prettyPrint(Declaration f:variables(t, frags), str indent){
	code = "";
	for(m <- (f@modifiers ? [])){
		code += prettyPrint(m,indent);
		code += " ";
	}
	code += prettyPrint(t,indent);
	code += " ";
	for(fr <- frags){
		code += prettyPrint(fr,indent);
		code += ", ";
	}
	return substring(code, 0, findLast(code, ","));
}

str prettyPrint(Declaration p:parameter(t, name, ext), "")
	= prettyPrint(t,"") + " "+name;

default str prettyPrint(Declaration d, str indent){
	println("Unknown declaration: <d>");
	return "";
}

//Expression
str prettyPrint(Expression s:arrayAccess(name, exp), str indent)
	 = prettyPrint(name, indent) + "[" + prettyPrint(exp,indent) + "]";

str prettyPrint(Expression s:newArray(t, ds), str indent){
	code = " new ";
	code += prettyPrint(t,indent);
	code+="[";
	for(d <-ds)
		code += prettyPrint(d,indent);
	code+="]";
	return code;
}

str prettyPrint(Expression e:assignment(lhs, operator, rhs), str indent)
	= prettyPrint(lhs,indent) + " " + operator + " " + prettyPrint(rhs,indent);

str prettyPrint(Expression e:newObject(Type name, list[Expression] args, Declaration decl), str indent){
	code = "new " + prettyPrint(name, indent) + "(";
	if(args != []){
		for(arg <- args){
			code += prettyPrint(arg,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ") ";
	return code + trim(prettyPrint(decl,indent)) + "\n";
}

str prettyPrint(Expression e:newObject(name, args), str indent){
	code = "new " + prettyPrint(name,indent) + "(";
	if(args != []){
		for(arg <- args){
			code += prettyPrint(arg,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + ")";
}

str prettyPrint(Expression q:qualifiedName(qName,name), str indent)
	= prettyPrint(qName,indent) + "." + prettyPrint(name,indent);
	
str prettyPrint(Expression e:conditional(c,ifB,elseB), str indent)
	= prettyPrint(c,indent) + " ? " + prettyPrint(ifB,indent) + " : " + prettyPrint(elseB,indent);

str prettyPrint(Expression v:fieldAccess(_, name), str indent)
	= name;
	
str prettyPrint(Expression v:fieldAccess(_, exp, name), str indent)
	= prettyPrint(exp,indent) + "." + name;

str prettyPrint(Expression m:methodCall(_, name, ps), str indent){
	code = name+"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + ")";
}

str prettyPrint(Expression m:methodCall(_, rec, name, ps), str indent){
	code = prettyPrint(rec,indent);
	code += "."+name+"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p,indent);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ")";
	return code;
}

str prettyPrint(Expression e:\null(), str indent)
	= "null";
	
str prettyPrint(Expression e:number(n), str indent)
	= n;

str prettyPrint(Expression e:booleanLiteral(b), str indent){
	if(b)
		return "true";
	else
		return "false";
}

str prettyPrint(Expression e:stringLiteral(s), str indent)
	= s;

str prettyPrint(Expression v:\type(exp), str indent)
	= prettyPrint(exp,indent) + ".class";

str prettyPrint(Expression v:variable(name,_), str indent)
	= name;

str prettyPrint(Expression v:variable(name,_, init), str indent)
	= name + " = " + prettyPrint(init,indent);
	
str prettyPrint(Expression b:\bracket(exp), str indent)
	= "(" + prettyPrint(exp,indent) + ")";

str prettyPrint(Expression v:this(), str indent)
	= "this";

str prettyPrint(Expression e:declarationExpression(exp), str indent)
	= prettyPrint(exp,"");

str prettyPrint(Expression e:infix(lhs,operator, rhs, exts), str indent){
	operator = " " + operator + " ";
	code = prettyPrint(lhs,indent);
	code += operator;
	code += prettyPrint(rhs,indent);
	for(ex <- exts){
		code += operator;
		code += prettyPrint(ex,indent);
	}
	return code;
}

str prettyPrint(Expression e:prefix(operator, operand), str indent)
	= operator + " " + prettyPrint(operand,indent);

str prettyPrint(Expression e:postfix(operand, operator), str indent)
	= prettyPrint(operand,indent) + " " + operator;

str prettyPrint(Expression e:simpleName(name), str indent)
	= name;

default str prettyPrint(Expression s, str indent){
	println("Unknown expression: <s>");
	return "";
}
	
	
//Statements
str prettyPrint(Statement s:block(stmts), str indent) {
	code = indent + "{\n";
	for(stmt <- stmts)
		code += prettyPrint(stmt, indent+"\t");
	return code + indent + "}\n";
}

str prettyPrint(Statement s:\break(""), str indent)
	= indent + "break;\n";

str prettyPrint(Statement s:\continue(), str indent)
	= indent + "continue;\n";
	
str prettyPrint(Statement s:empty(), str indent)
	= indent + ";\n";

str prettyPrint(Statement s:foreach(p, col, body), str indent)
	= indent + "for(" + prettyPrint(p,"") + " : "+ prettyPrint(col, indent) +") " + trim(prettyPrint(body, indent)) +"\n";

str prettyPrint(Statement s:\for(init, cond, update, body), str indent){
	code = indent;
	code += "for(";
	if(init != []){
		for(i <- init){
			code += prettyPrint(i, indent);
			code += ",";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += "; ";
	code += prettyPrint(cond,indent);
	code += "; ";
	if(update != []){
		for(u <- update){
			code += prettyPrint(u,indent);
			code += ",";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ") ";
	return code + trim(prettyPrint(body,indent)) + "\n";		
}

str prettyPrint(Statement s:\if(cond, b), str indent)
	= indent + "if(" + prettyPrint(cond,indent) + ") " + trim(prettyPrint(b, indent)) + "\n";

str prettyPrint(Statement s:\if(cond, b, eb), str indent)
	= indent + "if(" + prettyPrint(cond,indent) + ") " + trim(prettyPrint(b, indent)) + "\n" + indent + "else " +trim(prettyPrint(eb, indent)) + "\n";

str prettyPrint(Statement s:\return(exp), str indent)
	= indent + "return " + prettyPrint(exp,indent) + ";\n";
	
str prettyPrint(Statement s:\return(), str indent)
	= indent + "return;\n";

str prettyPrint(Statement s:synchronizedStatement(l, body), indent)
	= indent + "synchronized(" +	prettyPrint(l,indent) + ") " + trim(prettyPrint(body, indent)) + "\n";
	
str prettyPrint(Statement s:\try(body, catchClauses), indent){
	code = indent + "try " + trim(prettyPrint(body, indent)) + "\n";
	for(cs <- catchClauses){
		code += prettyPrint(cs, indent);
	}
	return code;
}

str prettyPrint(Statement s:\throw(exp), str indent)
	= indent + "throw " + prettyPrint(exp,indent) + ";\n";

str prettyPrint(Statement s:\try(body, catchClauses, fin), indent){
	code = indent + "try " + trim(prettyPrint(body, indent)) + "\n";
	for(cs <- catchClauses){
		code += prettyPrint(cs, indent);
	}
	code += indent + "finally " + trim(prettyPrint(fin, indent)) + "\n";
	return code;
}
	
str prettyPrint(Statement s:\catch(p, body), indent)
	= indent + "catch(" + prettyPrint(p, "") + ") " + trim(prettyPrint(body, indent)) + "\n";
	
str prettyPrint(Statement s:declarationStatement(e), str indent)
	= indent + prettyPrint(e, indent) + ";\n";

str prettyPrint(Statement s:\while(cond, stmt), str indent)
	= indent + "while(" + prettyPrint(cond, indent) + ") " + trim(prettyPrint(stmt, indent)) + "\n";	

str prettyPrint(Statement s:expressionStatement(e), str indent)
	= indent + prettyPrint(e, indent) + ";\n";
	
default str prettyPrint(Statement s, str indent){
	println("Unknown statement: <s>");
	return "";
}


//Type
str prettyPrint(Type i:\arrayType(t), str indent)
	= prettyPrint(t, indent) + "[] ";
	
str prettyPrint(Type i:parameterizedType(t), str indent)
	= prettyPrint(t, indent); 
	
str prettyPrint(Type s:simpleType(exp), str indent){
	code = prettyPrint(exp,indent);
	gs = getGenerics(exp@typ);
	if(gs != []){
		code += "\<";
		for(g <- gs){
			code += substring(g.path,findLast(g.path,"/"+1)) + ",";
		}
		code = substring(code, 0, findLast(code, ","));
		code += "\>";
	}
	return code;
}


str prettyPrint(Type i:\int(), str indent)
	= "int";

str prettyPrint(Type i:\long(), str indent)
	= "long";
	
str prettyPrint(Type i:\void(), str indent)
	= "void";

str prettyPrint(Type i:\boolean(), str indent)
	= "boolean";
	
default str prettyPrint(Type i){
	println("Unknown type: <i>");
	return "";
}

//Modifiers
str prettyPrint(Modifier m:\private(), str indent)
	= "private";	

str prettyPrint(Modifier m:\final(), str indent)
	= "final";	

str prettyPrint(Modifier m:\synchronized(), str indent)
	= "synchronized";	

str prettyPrint(Modifier m:\public(), str indent)
	= "public";	

str prettyPrint(Modifier m:\static(), str indent)
	= "static";	

str prettyPrint(Modifier m:\volatile(), str indent)
	= "volatile";	

default str prettyPrint(Modifier m, str indent){
	println("Unknown modifier: <m>");
	return "";
}

list[loc] getGenerics(TypeSymbol c:class(_, ls), str indent)
	= [l | class(l,_) <- ls];
list[loc] getGenerics(TypeSymbol c:interface(_, ls), str indent)
	= [l | class(l,_) <- ls];
default list[loc] getGenerics(TypeSymbol c)
	= [];