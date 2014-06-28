module PrettyPrint

import IO;
import String;
import lang::java::jdt::m3::AST;

loc targetFile = |project://rascal-refactoring/RefactoredCode|;
str code = "";

void prettyPrint(set[Declaration] asts, str ident){
	for(a <- asts)
		prettyPrint(a, ident);
}

void prettyPrint(list[Declaration] asts, str ident){
	for(a <- asts)
		prettyPrint(a, ident);
}

void prettyPrint(Declaration c:compilationUnit(imps, typs), str ident){
	targetFile = |project://rascal-refactoring/RefactoredCode|;
	targetFile.path = targetFile.path + c@decl.path;
	println("Creating file: <targetFile>");
	prettyPrint(imps, "");
	prettyPrint(typs, "");
	writeFile(targetFile,code);
	code = "";
}

void prettyPrint(Declaration c:compilationUnit(package, imps, typs), str ident){
		targetFile = |project://rascal-refactoring/RefactoredCode|;
		targetFile.path = targetFile.path + c@decl.path;
		println("Creating file: <targetFile>");
		code += "package ";
		prettyPrint(package, "");
		code += ";\n";
		prettyPrint(imps, "");
		prettyPrint(typs, "");
		writeFile(targetFile,code);
		code = "";
}

void prettyPrint(Declaration p:package(name), ident){
	code += name;
}
		
void prettyPrint(Declaration p:package(pp, name), ident){
	prettyPrint(pp);
	code += "."+name;
}

void prettyPrint(Declaration i:\import(name), str ident){
	code += "import " + name + ";\n";
}

void prettyPrint(Declaration c:\class(name, exts, impls, body), str ident){
	code += ident;
	for(m <- (c@modifiers ? [])){
		prettyPrint(m);
	}
	code += "class " + name;
	if(exts != []){
		code += " extends ";
		for(e <- exts){
			prettyPrint(e);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	if(impls != []){
		code += " implements ";
		for(i <- impls){
			prettyPrint(i);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += " {\n";
	prettyPrint(body, ident + "\t");
	code += "\n}";
}

void prettyPrint(Declaration f:field(t, frags), str ident){
	code += ident;
	for(m <- (f@modifiers ? [])){
		prettyPrint(m);
	}
	prettyPrint(t);
	code += " ";
	for(fr <- frags){
		prettyPrint(fr);
		code += ", ";
	}
	code = substring(code, 0, findLast(code, ",")) + ";\n";
}

void prettyPrint(Declaration f:variables(t, frags), str ident){
	prettyPrint(t);
	code += " ";
	for(fr <- frags){
		prettyPrint(fr);
		code += ", ";
	}
	code = substring(code, 0, findLast(code, ","));
}

void prettyPrint(Declaration m:method(t, name, ps, exs), ident){
	code += ident;
	for(modi <- (m@modifiers ? [])){
		prettyPrint(modi);
	}
	prettyPrint(t);
	code += name +"(";
	if(ps != []){
		for(p <- ps){
			prettyPrint(p);
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
	code += ";";
}

void prettyPrint(Declaration m:method(t, name, ps, exs, body), str ident){
	code += ident;
	for(modi <- (m@modifiers ? [])){
		prettyPrint(modi);
	}
	prettyPrint(t);
	code += name +"(";
	if(ps != []){
		for(p <- ps){
			prettyPrint(p);
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
	code += "\n";
	prettyPrint(body, ident + "\t");
}

void prettyPrint(Declaration p:parameter(t, name, ext)){
	prettyPrint(t);
	code += " "+name;
}

default void prettyPrint(Declaration d, str ident){
	println(d);
}

void prettyPrint(Type s:simpleType(exp)){
	prettyPrint(exp);
}

void prettyPrint(Type i:\int()){
	code += "int ";
}

void prettyPrint(Type i:\arrayType(t)){
	prettyPrint(t);
	code += "[] ";
}

void prettyPrint(Type i:\void()){
	code += "void ";
}

void prettyPrint(Type i:\boolean()){
	code += "boolean ";
}

void prettyPrint(Expression v:variable(name,_)){
	code += name;
}

void prettyPrint(Expression v:this()){
	code += "this";
}

void prettyPrint(Expression v:fieldAccess(_, exp, name)){
	prettyPrint(exp);
	code += "."+name;
}

void prettyPrint(Expression v:fieldAccess(_, name)){
	code += name;
}

void prettyPrint(Expression v:\type(exp)){
	prettyPrint(exp);
	code += ".class";
}


void prettyPrint(Expression v:variable(name,_, init)){
	code += name + " = ";
	prettyPrint(init);
}

void prettyPrint(Expression e:simpleName(name)){
	code += name;
}

void prettyPrint(Expression e:number(n)){
	code += n;
}

void prettyPrint(Expression e:booleanLiteral(b)){
	if(b)
		code += "true";
	else
		code += "false";
}

void prettyPrint(Expression e:infix(lhs,operator, rhs, exts)){
	operator = " " + operator + " ";
	prettyPrint(lhs);
	code += operator;
	prettyPrint(rhs);
	for(ex <- exts){
		code += operator;
		prettyPrint(ex);
	}
}

void prettyPrint(Expression e:prefix(operator, operand)){
	code += operator;
	prettyPrint(operand);
}

void prettyPrint(Expression e:postfix(operand, operator)){
	prettyPrint(operand);
	code += operator;
}

void prettyPrint(Expression e:infix(operator, operand)){
	code += operator;
	prettyPrint(operand);
}

void prettyPrint(Expression e:assignment(lhs,operator, rhs)){
	operator = " " + operator + " ";
	prettyPrint(lhs);
	code += operator;
	prettyPrint(rhs);
}

void prettyPrint(Expression m:methodCall(_, rec, name, ps)){
	prettyPrint(rec);
	code += "."+name+"(";
	if(ps != []){
		for(p <- ps){
			prettyPrint(p);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ")";
}

void prettyPrint(Expression q:qualifiedName(qName,name)){
	prettyPrint(qName);
	code += ".";
	prettyPrint(name);
}

void prettyPrint(Expression b:\bracket(exp)){
	code += "(";
	prettyPrint(exp);
	code += ")";
}

void prettyPrint(Statement s:empty(),_){
code += ";";
}

void prettyPrint(Statement s:\while(cond, stmt), str ident){
	code += ident;
	code += "while(";
	prettyPrint(cond);
	code += ")";
	prettyPrint(stmt, ident + "\t");
}

default void prettyPrint(Statement s, str ident){
	println(s);
}

void prettyPrint(Expression e:newObject(t,ps)){
	code += "new ";
	prettyPrint(t);
	code += "(";
	if(ps != []){
		for(p <- ps){
			prettyPrint(p);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ",")) + ")";
	}
	code += ")";
}

void prettyPrint(Expression m:methodCall(_, name, ps)){
	code += name+"(";
	if(ps != []){
		for(p <- ps){
			prettyPrint(p);
			code += ", ";
		}
		code = substring(code, 0, findLast(code, ","));
	}
	code += ")";
}

default void prettyPrint(Expression s){
	println(s);
}

void prettyPrint(Statement s:\if(cond, b), str ident){
	code += ident;
	code += "if(";
	prettyPrint(cond);
	code += ")\n ";
	prettyPrint(b, ident);
}

void prettyPrint(Statement s:block(stmts), str ident){
	code += ident;
	code += "{\n";
	for(stmt <- stmts)
		prettyPrint(stmt, ident+"\t");
	code += ident + "}\n";
}

void prettyPrint(Statement s:expressionStatement(e), str ident){
		code += ident;
		prettyPrint(e);
		code += ";\n";
}

void prettyPrint(Statement s:declarationStatement(e), str ident){
		code += ident;
		prettyPrint(e, ident);
		code += ";\n";
}

void prettyPrint(Statement s:synchronizedStatement(l, body), ident){
	code += ident;
	code += "synchronized(";
	prettyPrint(l);
	code += ")\n";
	prettyPrint(body, ident + "\t");
}

void prettyPrint(Modifier m:\private()){
	code += "private ";	
}

void prettyPrint(Modifier m:\synchronized()){
	code += "synchronized ";	
}

void prettyPrint(Modifier m:\public()){
	code += "public ";	
}

void prettyPrint(Modifier m:\static()){
	code += "static ";	
}

void prettyPrint(Modifier m:\volatile()){
	code += "volatile ";	
}

default void prettyPrint(Modifier m){
	println(m);
}