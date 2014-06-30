module refactoring::introducing_shared_state::ConvertLocalToField

import IO;
import Set;
import String;

import PrettyPrint;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::Java2DFG;
import lang::sccfg::converter::util::Getters;

import refactoring::microrefactorings::GetInfo;
import refactoring::rearranging_code::GenerateIds;
import refactoring::microrefactorings::MicroRefactorings;

Declaration newFieldDeclaration;

set[Declaration] convertLocalToField(set[Declaration] asts, loc local){
	<targetedClassDecl, targetedMethodDecl, newFieldDecl, lockDecl> = findDeclarations(local);
	
	refactoredAst = top-down-break visit(asts){
		case c:class(name, exts, impls ,body):{
			if(c@decl == targetedClassDecl){
				body = for(b <- body){
					append(convertLocalToField(b, local, targetedMethodDecl, newFieldDecl, lockDecl));
				}
				body = [Declaration::field(simpleType(simpleName("Object")[@decl=|java+class:///java/lang/Object|][@typ=object()]),[variable(extractVariableNameFromDecl(lockDecl), 0, newObject(simpleType(simpleName("Object")[@decl=|java+class:///java/lang/Object|][@typ=object()][@src = generateId(c@src)]),[])[@src = generateId(c@src)])[@decl = lockDecl][@src = generateId(c@src)]])[@modifiers = [Modifier::\private()]]]
					 + [newFieldDeclaration]
				     + body;
				insert class(name, exts, impls ,body)[@modifiers=c@modifiers][@src = c@src][@decl=c@decl][@typ=c@typ];
			}
			else
				fail;
		}
	}
	
	p = createDFG(asts);
	pR = createDFG(refactoredAst);
		
	if(checkConvertLocalToField(p,pR, local)){
		println("Refactoring ConvertLocalToField successful!");
		prettyPrint(refactoredAst,"");
		return refactoredAst;
	}
	else{
		println("Refactoring failed!");
		return asts;
	}
}

Declaration convertLocalToField(Declaration f:field(t,frags), loc local, loc targetedMethodDecl, loc newFieldDecl, loc lockDecl){
	for(fr <- frags){
		if(fr@decl == newFieldDecl)
			throw "Field with name <fieldName> already exists at <f@src>";
		if(fr@decl == lockDecl)
			throw "Field with name generated_lock_for_<fieldName> already exists at <f@src>";
	}
	return f;
}

Declaration convertLocalToField(Declaration m:method(r, n, ps, exs, mb), loc local, loc targetedMethodDecl, loc newFieldDecl, loc lockDecl){
	if(m@decl == targetedMethodDecl){
		locking = simpleName(extractVariableNameFromDecl(lockDecl))[@decl = lockDecl][@typ = object()];
		<mb, newFieldDeclaration> = encloseInASynchronizedBlock(mb, local, newFieldDecl, locking);
		if(!(Stmt::block(_) := mb))
			mb = block([mb])[@src = mb@src];
		return method(r, n, ps, exs, mb)[@src = m@src][@decl = m@decl][@typ = m@typ][@modifiers = m@modifiers];
	}
	else
		return m;
}

default Declaration convertLocalToField(Declaration d, loc local, loc targetedMethodDecl, loc newfieldDecl, loc lockDecl)
	= d;
	
private tuple[loc, loc, loc, loc] findDeclarations(loc local){
	loc targetedMethodDecl = getMethodDeclFromVariable(local);
	loc targetedClassDecl = getClassDeclFromMethod(targetedMethodDecl);
	str fieldName = extractVariableNameFromDecl(local);
	loc newFieldDecl = createNewFieldDeclaration(targetedClassDecl, fieldName);
	loc lockDecl = createNewFieldDeclaration(targetedClassDecl, "generated_lock_for_"+fieldName);
	return <targetedClassDecl, targetedMethodDecl, newFieldDecl, lockDecl>;
}

bool checkConvertLocalToField(Program original, Program refactored, loc local){
	//The only changes in declarations are the two added fields
	dif = refactored.decls - original.decls;

	loc l;
	loc var;
	for(attribute(name, _) <- dif){
		if(contains(name.path,"generated"))
			l = name;
		else
			var = name;
	}
	
	if(original.decls - refactored.decls != {} && size(dif) == 2){
		println("Error: Missing fields");
		return false;
	}
	
	//Map all accesses to local to the field
	if(!mapAccessesOfLocalToField(original, local, refactored, var)){
		println("Missing accesses");
		return false;
	}
	
	//No synchronization edges lost
	origSynch = getSynchronizationActions(original);
	refactSynch = getSynchronizationActions(refactored);
	if(origSynch - refactSynch != {}){
		println("Error: Synchronization edges lost!");
		return false;
	}
	
	//The only new synchronization edges consern the lock, and there is only one id two ids one of the block and possible ones in assignment
	if(removeAllSynchronizationEdgesOfWithTheSameId(refactSynch, l) - origSynch != {}){
		println("Error: Synchronization Stmt gained unwanted synchronization edges!");
		return false;
	}
	
	//Any access of the new field has an acquire and a release dependency with the lock
	if(accessOf_AlwaysSynchronizedBy_(refactored, var, l)){
		println("Error: unguarded access of new field!");
		return false;
	}
	
	return true;
}

bool accessOf_AlwaysSynchronizedBy_(Program p, loc var, loc l){
	accesses = { getIdFromStmt(stmt) | stmt <- p.statements, getVarFromStmt(stmt) == var};
	guarded = { stmt | stmt <- p.statements, getVarFromStmt(stmt) == l, getDependencyFromStmt(stmt) in accesses, !isDataAccess(stmt)};
	return size(accesses) == size(guarded);
}

set[Stmt] removeAllSynchronizationEdgesOfWithTheSameId(set[Stmt] stmts, loc var){
	loc src;
	for(stmt <- stmts){
		if(var == getVarFromStmt(stmt)){
			src = getIdFromStmt(stmt);
			break;
		}
	}
	return { stmt | stmt <- stmts, src != getIdFromStmt(stmt), src != getDependencyFromStmt(stmt), getDependencyFromStmt(stmt).length > 0};
	
}

bool mapAccessesOfLocalToField(Program original, loc local, Program refactored, loc var){
	accesses = { <getIdFromStmt(stmt), getDependencyFromStmt(stmt)> | stmt <- original.statements, getVarFromStmt(stmt) == local};
	newAccesses = { <getIdFromStmt(stmt), getDependencyFromStmt(stmt)> | stmt <- refactored.statements, getVarFromStmt(stmt) == var};
	return accesses == newAccesses;
}