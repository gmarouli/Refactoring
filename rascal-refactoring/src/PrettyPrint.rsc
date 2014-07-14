module PrettyPrint

import IO;
import String;
import lang::java::jdt::m3::AST;

loc targetFile = |project://rascal-refactoring/RefactoredCode|;

void prettyPrint(set[Declaration] asts){
	for(a <- asts)
		prettyPrint(a, "");
}

str prettyPrint(list[Declaration] asts, str ident){
	code = "";
	for(a <- asts)
		code += prettyPrint(a, ident);
	return code;
}

//Declarations
void prettyPrint(Declaration c:compilationUnit(imps, typs), str ident){
	targetFile = |project://rascal-refactoring/RefactoredCode|;
	targetFile.path = targetFile.path + c@decl.path;
	println("Creating file: <targetFile>");
	code = prettyPrint(imps, "");
	code += prettyPrint(typs, "");
	writeFile(targetFile,code);
}

void prettyPrint(Declaration c:compilationUnit(package, imps, typs), str ident){
		targetFile = |project://rascal-refactoring/RefactoredCode|;
		targetFile.path = targetFile.path + c@decl.path;
		println("Creating file: <targetFile>");
		code = "package "+prettyPrint(package, "") + ";\n";
		code += prettyPrint(imps, "");
		code += prettyPrint(typs, "");
		writeFile(targetFile,code);
}

str prettyPrint(Declaration c:\class(name, exts, impls, body), str ident){
	code = ident;
	for(m <- (c@modifiers ? [])){
		code += prettyPrint(m);
		code += " ";
	}
	code += "class " + name;
	if(exts != []){
		code += " extends ";
		for(e <- exts){
			code += prettyPrint(e);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	if(impls != []){
		code += " implements ";
		for(i <- impls){
			code += prettyPrint(i);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += " {\n";
	code += prettyPrint(body, ident + "\t");
	code += "\n}";
	return code;
}

str prettyPrint(Declaration f:field(t, frags), str ident){
	code = ident;
	for(m <- (f@modifiers ? [])){
		code += prettyPrint(m);
		code += " ";
	}
	code += prettyPrint(t);
	code += " ";
	for(fr <- frags){
		code += prettyPrint(fr);
		code += ", ";
	}
	code = substring(code, 0, findLast(code, ",")) + ";\n";
	return code;
}


str prettyPrint(Declaration p:package(name), ident){
	return name;
}

str prettyPrint(Declaration m:method(t, name, ps, exs), ident){
	code = "\n"+ident;
	for(modi <- (m@modifiers ? [])){
		code += prettyPrint(modi);
		code += " ";
	}
	code += prettyPrint(t);
	code += name +"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ",")) + ")";
	}
	if(exs != []){
		code += " throws ";
		for(e <- exs){
			prettyPrint(e);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + ";\n";
}

str prettyPrint(Declaration m:method(t, name, ps, exs, body), str ident){
	code = "\n" + ident;
	for(modi <- (m@modifiers ? [])){
		code += prettyPrint(modi);
		code += " ";
	}
	code += prettyPrint(t);
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
			prettyPrint(e);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + trim(prettyPrint(body, ident))+"\n";
}

str prettyPrint(Declaration s:constructor(name, ps, exs, body), ident){
	code = "\n" + ident;
	for(modi <- (s@modifiers ? [])){
		code += prettyPrint(modi);
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
			code += prettyPrint(e);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + trim(prettyPrint(body, ident)) + "\n";
}

str prettyPrint(Declaration i:\import(name), str ident)
	= "import " + name + ";\n";
	
str prettyPrint(Declaration p:package(pp, name), ident)
	= prettyPrint(pp) + "." + name;

str prettyPrint(Declaration f:variables(t, frags), str ident){
	code = "";
	for(m <- (f@modifiers ? [])){
		code += prettyPrint(m);
		code += " ";
	}
	code += prettyPrint(t);
	code += " ";
	for(fr <- frags){
		code += prettyPrint(fr);
		code += ", ";
	}
	return substring(code, 0, findLast(code, ","));
}

str prettyPrint(Declaration p:parameter(t, name, ext), "")
	= prettyPrint(t) + " "+name;

default str prettyPrint(Declaration d, str ident){
	println("Unknown declaration: <d>");
	return "";
}

//Expression
str prettyPrint(Expression s:arrayAccess(name, exp))
	 = prettyPrint(name) + "[" + prettyPrint(exp) + "]";

str prettyPrint(Expression s:newArray(t, ds)){
	code = " new ";
	code += prettyPrint(t);
	code+="[";
	for(d <-ds)
		code += prettyPrint(d);
	code+="]";
	return code;
}

str prettyPrint(Expression e:assignment(lhs, operator, rhs))
	= prettyPrint(lhs) + " " + operator + " " + prettyPrint(rhs);

str prettyPrint(Expression e:newObject(name, args)){
	code = "new " + prettyPrint(name) + "(";
	if(args != []){
		for(arg <- args){
			code += prettyPrint(arg);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + ")";
}

str prettyPrint(Expression q:qualifiedName(qName,name))
	= prettyPrint(qName) + "." + prettyPrint(name);
	

str prettyPrint(Expression v:fieldAccess(_, name))
	= name;
	
str prettyPrint(Expression v:fieldAccess(_, exp, name))
	= prettyPrint(exp) + "." + name;

str prettyPrint(Expression m:methodCall(_, name, ps)){
	code = name+"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	return code + ")";
}

str prettyPrint(Expression m:methodCall(_, rec, name, ps)){
	code = prettyPrint(rec);
	code += "."+name+"(";
	if(ps != []){
		for(p <- ps){
			code += prettyPrint(p);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ")";
	return code;
}

str prettyPrint(Expression e:\null())
	= "null";
	
str prettyPrint(Expression e:number(n))
	= n;

str prettyPrint(Expression e:booleanLiteral(b)){
	if(b)
		return "true";
	else
		return "false";
}

str prettyPrint(Expression e:stringLiteral(s))
	= s;

str prettyPrint(Expression v:\type(exp))
	= prettyPrint(exp) + ".class";

str prettyPrint(Expression v:variable(name,_))
	= name;

str prettyPrint(Expression v:variable(name,_, init))
	= name + " = " + prettyPrint(init);
	
str prettyPrint(Expression b:\bracket(exp))
	= "(" + prettyPrint(exp) + ")";

str prettyPrint(Expression v:this())
	= "this";

str prettyPrint(Expression e:declarationExpression(exp))
	= prettyPrint(exp,"");

str prettyPrint(Expression e:infix(lhs,operator, rhs, exts)){
	operator = " " + operator + " ";
	code = prettyPrint(lhs);
	code += operator;
	code += prettyPrint(rhs);
	for(ex <- exts){
		code += operator;
		code += prettyPrint(ex);
	}
	return code;
}

str prettyPrint(Expression e:prefix(operator, operand))
	= operator + " " + prettyPrint(operand);

str prettyPrint(Expression e:postfix(operand, operator))
	= prettyPrint(operand) + " " + operator;

str prettyPrint(Expression e:simpleName(name))
	= name;

default str prettyPrint(Expression s){
	println("Unknown expression: <s>");
	return "";
}
	
	
//Statements
str prettyPrint(Statement s:block(stmts), str ident) {
	code = ident + "{\n";
	for(stmt <- stmts)
		code += prettyPrint(stmt, ident+"\t");
	return code + ident + "}\n";
}

str prettyPrint(Statement s:\break(""), str ident)
	= ident + "break;\n";

str prettyPrint(Statement s:\continue(), str ident)
	= ident + "continue;\n";
	
str prettyPrint(Statement s:empty(),_)
	= ";\n";

str prettyPrint(Statement s:\for(init, cond, update, body), str ident){
	code = ident;
	code += "for(";
	if(init != []){
		for(i <- init){
			code += prettyPrint(i);
			code += ",";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += "; ";
	code += prettyPrint(cond);
	code += "; ";
	if(update != []){
		for(u <- update){
			code += prettyPrint(u);
			code += ",";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ") ";
	return code + trim(prettyPrint(body,ident)) + "\n";		
}

str prettyPrint(Statement s:\if(cond, b), str ident)
	= ident + "if(" + prettyPrint(cond) + ") " + trim(prettyPrint(b, ident)) + "\n";

str prettyPrint(Statement s:\if(cond, b, eb), str ident)
	= ident + "if(" + prettyPrint(cond) + ") " + trim(prettyPrint(b, ident)) + "\n" + ident + "else " +trim(prettyPrint(eb, ident)) + "\n";

str prettyPrint(Statement s:\return(exp), str ident)
	= ident + "return " + prettyPrint(exp) + ";\n";
	
str prettyPrint(Statement s:\return(), str ident)
	= ident + "return;\n";

str prettyPrint(Statement s:synchronizedStatement(l, body), ident)
	= ident + "synchronized(" +	prettyPrint(l) + ") " + trim(prettyPrint(body, ident)) + "\n";
	
str prettyPrint(Statement s:\try(body, catchClauses), ident){
	code = ident + "try " + trim(prettyPrint(body, ident)) + "\n";
	for(cs <- catchClauses){
		code += prettyPrint(cs, ident);
	}
	return code;
}

str prettyPrint(Statement s:\try(body, catchClauses, fin), ident){
	code = ident + "try " + trim(prettyPrint(body, ident)) + "\n";
	for(cs <- catchClauses){
		code += prettyPrint(cs, ident);
	}
	code += ident + "finally " + trim(prettyPrint(fin, ident)) + "\n";
	return code;
}
	
str prettyPrint(Statement s:\catch(p, body), ident)
	= ident + "catch(" + prettyPrint(p, "") + ") " + trim(prettyPrint(body, ident)) + "\n";
	
str prettyPrint(Statement s:declarationStatement(e), str ident)
	= ident + prettyPrint(e, ident) + ";\n";

str prettyPrint(Statement s:\while(cond, stmt), str ident)
	= ident + "while(" + prettyPrint(cond) + ") " + trim(prettyPrint(stmt, ident)) + "\n";	

str prettyPrint(Statement s:expressionStatement(e), str ident)
	= ident + prettyPrint(e) + ";\n";
	
default str prettyPrint(Statement s, str ident){
	println("Unknown statement: <s>");
	return "";
}


//Type
str prettyPrint(Type i:\arrayType(t))
	= prettyPrint(t) + "[] ";
	
str prettyPrint(Type s:simpleType(exp))
	= prettyPrint(exp);


str prettyPrint(Type i:\int())
	= "int";

str prettyPrint(Type i:\void())
	= "void";

str prettyPrint(Type i:\boolean())
	= "boolean";

//Modifiers
str prettyPrint(Modifier m:\private())
	= "private";	

str prettyPrint(Modifier m:\final())
	= "final";	

str prettyPrint(Modifier m:\synchronized())
	= "synchronized";	

str prettyPrint(Modifier m:\public())
	= "public";	

str prettyPrint(Modifier m:\static())
	= "static";	

str prettyPrint(Modifier m:\volatile())
	= "volatile";	

default str prettyPrint(Modifier m){
	println("Unknown modifier: <m>");
	return "";
}