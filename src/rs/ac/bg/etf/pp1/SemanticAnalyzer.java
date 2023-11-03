package rs.ac.bg.etf.pp1;
import org.apache.log4j.Logger;

import java.util.*;
import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;


public class SemanticAnalyzer extends VisitorAdaptor {

	private Object object;
	boolean errorDetected = false;
	int printCallCount = 0;
	Obj currentMethod = null;
	Struct currentType=null;
	public static Struct BoolStruct=new Struct(Struct.Bool);
	boolean returnFound = false;
	boolean main=false;
	boolean inLoop=false;
	int nLoop=0;
	int nBlocks=0;
	int nIfs=0;
	int nVars;
	
	int noFormalPars=0;
	int noActPars=0;
	
	
	Stack<Obj> functions= new Stack<Obj>();

	Logger log = Logger.getLogger(getClass());

	//Tab.insert(Obj.Type,"boolean",BoolType);
	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" na liniji ").append(line);
		log.error(msg.toString());
	}

	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message); 
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" na liniji ").append(line);
		log.info(msg.toString());
	}
	
	public void visit(Program program) {		
		nVars = Tab.currentScope.getnVars();
		if(Tab.currentScope.findSymbol("main")== null) {
			report_error("ERROR! Main metoda nije pronadjena!!!",null);
		}else {
			if(Tab.find("main").getType() != Tab.noType) {
				//report_error("Error! Main metoda nije tipa void ", null);
			}else {
				if(Tab.find("main").getLevel()!=0) {
					report_error("Error! Main metoda ne treba da ima argumente",null);
				}
			}
		}
		Tab.chainLocalSymbols(program.getProgName().obj);
		Tab.closeScope();
	}

	public void visit(ProgName progName) {
		progName.obj = Tab.insert(Obj.Prog, progName.getPName(), Tab.noType);
		Tab.openScope();     	
	}
	
	public void visit(VarEndClassic var) {
		if(Tab.currentScope.findSymbol(var.getVarName())!=null) {
			report_error("Error! Promenljiva sa nazivom "+var.getVarName()+ " je vec deklarisana",var);
		}
		else {
			Obj obj;
			obj = Tab.insert(Obj.Var,var.getVarName(),currentType);
			
			
			report_info("Deklarisana promenljiva "+ var, var);
			var.obj=obj;
		}
	}
	
	public void visit(VarEndArr varArray){
		if(Tab.currentScope.findSymbol(varArray.getVarName())!=null) {
			report_error("Error! Niz sa nazivom "+ varArray.getVarName()+" je vec deklarisan",varArray);
		}else {
			Obj obj;
			obj = Tab.insert(Obj.Var,varArray.getVarName(),new Struct(Struct.Array,currentType));
			varArray.obj=obj;
		}
		
		report_info("Deklarisana niz "+ varArray.obj.getType().getKind()+varArray.obj.getType().getElemType().getKind(), varArray);
	}
	public void visit(VarEndMat varMat) {
		if(Tab.currentScope.findSymbol(varMat.getVarName())!=null) {
			report_error("Error! Matrica sa nazivom "+varMat.getVarName()+" je vec deklarisana",varMat);
		}else {
			Obj obj;
			obj=Tab.insert(Obj.Var,varMat.getVarName(),new Struct(Struct.Array,currentType));
			varMat.obj=obj;
		}
		report_info("Deklarisana matrica "+  varMat.obj.getType().getKind()+varMat.obj.getType().getElemType().getKind(), varMat);
	}


	/*
	public void visit(VarDecl varDecl) {
		report_info("Deklarisana promenljiva "+ varDecl, varDecl);
		Obj varNode = Tab.insert(Obj.Var, var, varDecl.getType().struct);
	}
	
	*/
	public void visit(Type type) {
		Obj typeNode = Tab.find(type.getTypeName());
		if (typeNode == Tab.noObj && !type.getTypeName().equals("bool")) {
			report_error("Nije pronadjen tip " + type.getTypeName() + " u tabeli simbola", null);
			type.struct = Tab.noType;
		}
		else if(type.getTypeName().equals("bool")) {
			typeNode=Tab.insert(Obj.Type,"bool",BoolStruct);
			type.struct=BoolStruct;
			currentType=typeNode.getType();
		}
		else {
			if (Obj.Type == typeNode.getKind()) {
				type.struct = typeNode.getType();
				currentType=type.struct;
			} 
			else {
				report_error("Greska: Ime " + type.getTypeName() + " ne predstavlja tip ", type);
				type.struct = Tab.noType;
			}
		}  
	}

	public void visit(MethodDeclar methodDecl) {
		if (!returnFound && currentMethod.getType() != Tab.noType) {
			report_error("Semanticka greska na liniji " + methodDecl.getLine() + ": funcija " + currentMethod.getName() + " nema return iskaz!", null);
		}
		
		Tab.chainLocalSymbols(currentMethod);
		Tab.closeScope();
		
		returnFound = false;
		currentMethod = null;
		noFormalPars=0;
		
	}
	public void visit(NoReturn noret) {
		currentType=Tab.noType;
	}
	public void visit(MethodTypeName methodTypeName) {
		methodTypeName.obj=Tab.noObj;
		if(Tab.currentScope.findSymbol(methodTypeName.getMethName())!=null) {
			report_error("Error! Metod "+ methodTypeName.getMethName()+" je vec definsan",methodTypeName);
		}else {
			methodTypeName.obj=Tab.insert(Obj.Meth,methodTypeName.getMethName(),currentType);
			currentMethod = methodTypeName.obj;
			Tab.openScope();

			report_info("Obradjuje se funkcija " + methodTypeName.getMethName(), methodTypeName);
			report_info("Povratni arg"+currentType.getKind(),methodTypeName);
		}
	}

	
	
	
	public void visit(FormalParamVar formalParVar) {
		if(Tab.currentScope.findSymbol(formalParVar.getParamName())!=null) {
			report_error("Greska! Promenljiva "+formalParVar.getParamName()+ " je vec definisana.",formalParVar);
		}else {
			noFormalPars++;
			Obj obj=Tab.insert(Obj.Var,formalParVar.getParamName(),formalParVar.getType().struct);
			obj.setFpPos(noFormalPars);
			currentMethod.setLevel(noFormalPars);
		}
	}
	
	public void visit(FormalParamArray formalParamArr) {
		if(Tab.currentScope.findSymbol(formalParamArr.getParamName())!=null) {
			report_error("Greska! Niz "+formalParamArr.getParamName()+ " je vec definisan.",formalParamArr);
		}else {
			noFormalPars++;
			Obj obj=Tab.insert(Obj.Var,formalParamArr.getParamName(),new Struct(Struct.Array,currentType));
			obj.setFpPos(noFormalPars);
			currentMethod.setLevel(noFormalPars);
		}
	}
	public void visit(FormalParamMatrix formalParamMat) {
		if(Tab.currentScope.findSymbol(formalParamMat.getParamName())!=null) {
			report_error("Greska! Matrica "+formalParamMat.getParamName()+ " je vec definisana.",formalParamMat);
		}else {
			noFormalPars++;
			Obj obj=Tab.insert(Obj.Var,formalParamMat.getParamName(),new Struct(Struct.Array,currentType));
			obj.setFpPos(noFormalPars);
			currentMethod.setLevel(noFormalPars);
		}
	}
	
	public void visit(Break breakLoop) {
		if(nLoop==0) {
			report_error("Error! Break se ne nalazi unutar petlje",breakLoop);
		}
	}
	public void visit(Continue continueLoop) {
		if(!inLoop) {
			report_error("Error! Break se ne nalazi unutar petlje",continueLoop);
		}
	}
	
	public void visit(IfStart ifStart) {
		nBlocks++;
		nIfs++;
	}
	
	public void visit(ElseStart elseStart) {
		nIfs--;
		
	}
	public void visit(WhileStart whileStart) {
		nBlocks++;
		inLoop=true;
		nLoop++;
		report_info("Usli u petlj"+nLoop,whileStart);
	}
	public void visit(MapStart mapStart) {
		nBlocks++;
		inLoop=true;
		nLoop++;
	}
	
	public void visit(UnmatchedIf unif) {
		nBlocks--;
		nIfs--;
	}
	public void visit(UnmatchedIfElse unifelse) {
		nBlocks--;
	}
	public void visit(MatchedIf matif) {
		nBlocks--;
	}
	public void visit(MatchedWhile matwhile) {
		if(--nLoop==0) {
			inLoop=false;
		}

		report_info("Izasli iz petlj"+nLoop,matwhile);
		nBlocks--;
	}public void visit(UnmatchedWhile unmatwhile) {
		if(--nLoop==0) {
			inLoop=false;
		}

		report_info("Izasli iz petlj",unmatwhile);
		nBlocks--;
	}
	
	
	public void visit(Read readMatch) {
		if(readMatch.getDesignator().obj.getType()==Tab.intType||readMatch.getDesignator().obj.getType()==BoolStruct||readMatch.getDesignator().obj.getType()==Tab.charType) {
			if(readMatch.getDesignator().obj.getKind()==Obj.Var||readMatch.getDesignator().obj.getKind()==Obj.Fld||readMatch.getDesignator().obj.getKind()==Obj.Elem) {
				//sve ok
			}else {

				report_error("Error! Pogresna vrsta parametra",readMatch);
			}
		}else {
			report_error("Error! Pogresan tip parametra",readMatch);
		}
	}
	
	public void visit(MatchedPrint matchPrint) {
		if(matchPrint.getExpr().struct==Tab.intType||matchPrint.getExpr().struct==BoolStruct||matchPrint.getExpr().struct==Tab.charType) {
			//sve ok;
			printCallCount++;
			
		}else {
			report_error("Error! Nepravilan tip parametra" +matchPrint.getExpr().struct.getKind(),matchPrint);
		}
	}
	
	public void visit(ReturnExpr ret) {
		if(currentMethod==null) {
			report_error("Error! Return se ne nalazi u funkciji",ret);
		}else {
			if(currentMethod.getType()==ret.getExpr().struct) {
				//sve ok
				returnFound=true;
			}else {
				report_error("Error! Tip argumenta nije ekvivalentan tipu povratnog podatka",ret);
			}
		}
	}
	
	public void visit(ReturnNoExpr retno) {
		if(currentMethod==null) {
			report_error("Error! Return se ne nalazi u funkciji",retno);
		}else {
			if(currentMethod.getType()==Tab.noType) {
				returnFound=true;
			}else {
				report_error("Error! Metoda nije void!!!",retno);
			}
		}
	}
	
	public void visit(ConditionOR cor) {
		if(cor.getCondition2().struct!=BoolStruct||cor.getCondTerm().struct!=BoolStruct) {
			report_error("Error! Tipovi uslova za operaciju OR moraju biti bool!",cor);
		}
		cor.struct=BoolStruct;
	}
	
	public void visit(ConditionORTerm cort) {
		cort.struct=cort.getCondTerm().struct;
	}
	
	public void visit(ConditionAND cand) {
		if(cand.getCondTerm().struct!=BoolStruct||cand.getCondFact().struct!=BoolStruct) {
			report_error("Error! Tipovi uslova za operaciju AND moraju biti bool!",cand);
		}
		cand.struct=BoolStruct;
	}
	
	public void visit(ConditionANDFact candf) {
		candf.struct=candf.getCondFact().struct;
	}
	
	public void visit(CondFactRec cf) {
		if(!cf.getExpr().struct.compatibleWith(cf.getExpr1().struct)) {
			report_error("Ne mogu da se porede razlicite strukture podataka!!!",cf);
		}
		else {
			if((cf.getExpr().struct.getKind()==3||cf.getExpr().struct.getKind()==4
					||cf.getExpr1().struct.getKind()==3||cf.getExpr1().struct.getKind()==4)
					&&(cf.getRelop() instanceof RelopGre||cf.getRelop() instanceof RelopGreeq||
							cf.getRelop() instanceof RelopLe||cf.getRelop() instanceof RelopLeq)) {

				report_error("Nekompatibilan operator poredjenja sa vrstom operanada sa kojim se porede!!!",cf);
			}
		}
		cf.struct=BoolStruct;
	}
	public void visit(EndCondFact ecf) {
		if(ecf.getExpr().struct.equals(BoolStruct)) {
			ecf.struct=BoolStruct;
		}else {

			report_error("Vrednost izraza nije boolean!!!",ecf);
		}
	}
	public void visit(MapVar mapVar) {
		
		mapVar.obj=Tab.find(mapVar.getI1());
		if(mapVar.obj==Tab.noObj) {
			report_error("Dato ime ne postoji",mapVar);
		}
	}
	public void visit(Mapping map) {
		if(--nLoop==0) {
			inLoop=false;
		}
		nBlocks--;
		if(map.getDesignator().obj.getType().getKind()!=Struct.Array) {
			report_error("Error! Map se moze koristiti samo za nizove!!!",map);
		}
		else {
			if(!map.getDesignator().obj.getType().getElemType().equals(map.getMapVar().obj.getType())) {
				report_error("Error! Promenljiva nije istog tipa kao i elementi niza!!!",map);
			}
		}
	}
	public void visit(MinusTermExpr minusTerm) {
		if(minusTerm.getTerm().struct!=Tab.intType) {
			report_error("Error! Argument mora biti tipa int",minusTerm);
		}
		minusTerm.struct=Tab.intType;
	}
	
	public void visit(AddExpr addExpr) {
		if(addExpr.getExpr().struct!=Tab.intType ||addExpr.getTerm().struct!=Tab.intType) {
			report_error("Error! Nekompatibilni tipovi podataka kod sabiranja",addExpr);
		}
			addExpr.struct=Tab.intType;
	}
	public void visit(TermExpr termExpr) {

		termExpr.struct=termExpr.getTerm().struct;
	}
	
	public void visit(TermMul termMul) {
		if(termMul.getTerm().struct!=Tab.intType || termMul.getFactor().struct!= Tab.intType) {
			report_error("Error! Argument mnozenja mora biti tipa int",termMul);
		}
		termMul.struct=Tab.intType;
	}
	
	public void visit(TermNoMul termNoMul) {
		termNoMul.struct=termNoMul.getFactor().struct;
	}
	
	public void visit(FactorConst fc) {
		fc.struct=fc.getConstVal().obj.getType();
	}
	
	public void visit(FactorVar factVar) {
		factVar.struct=factVar.getDesignator().obj.getType();
	}
	public void visit(MaxArr maxArr) {
		if(maxArr.getDesignator().obj.getType().getKind()!=3) {
			report_error("Pored operatora ^ treba biti niz",maxArr);
		}
		maxArr.struct=maxArr.getDesignator().obj.getType().getElemType();
	}
	public void visit(FactorNew factNew) {
		if(factNew.getExpr().struct!=Tab.intType) {
			report_error("Error! Broj elemenata niza mora biti tipa int!",factNew);
		}else {
			factNew.struct=new Struct(Struct.Array,factNew.getType().struct);
		}
	}
	public void visit(FactorNewMat factNewMat) {
		if(factNewMat.getExpr().struct!=Tab.intType||factNewMat.getExpr1().struct!=Tab.intType) {
			report_error("Error! Broj elemenata matrice mora biti tipa int!",factNewMat);
		}else {
			factNewMat.struct=new Struct(Struct.Array,factNewMat.getType().struct);
		}
	}
	
	public void visit(FuncCall funcCall) {
		if(funcCall.getDesignator().obj.getLevel()!=noActPars) {
			report_error("Error! Pogesan broj argumenata!!! "+funcCall.getDesignator().obj.getLevel()+noActPars+funcCall.getDesignator().obj.getName(),funcCall);
		}else {
			funcCall.struct=funcCall.getDesignator().obj.getType();
			noActPars=0;
		}
	}
	
	public void visit(FactorParen factParen) {
		factParen.struct=factParen.getExpr().struct;
	}
	public void visit(ConstEnd constLeaf){
		if(Tab.currentScope.findSymbol(constLeaf.getCName())!=null) {
			report_error("Greska na liniji " +constLeaf.getLine()+" : konstanta je vec definisana.",null);
		}else {
			Obj obj;
			obj=Tab.insert(Obj.Con,constLeaf.getCName(),currentType);
			if(constLeaf.getConstVal().obj.getType().equals(obj.getType())) {
				obj.setAdr(constLeaf.getConstVal().obj.getAdr());
			}else {
				report_error("Error! Nekompatibilni tipovi!!!",constLeaf);
			}
			
			report_info("Deklarisana je konstanta " + constLeaf.getCName(),constLeaf);
		}
	}
	
	public void visit(ConstNum numConst) {
		//numConst.obj
		numConst.obj=new Obj(Obj.Con,"",Tab.intType);
		numConst.obj.setAdr(numConst.getValue());
	}
	public void visit(ConstChar charConst) {
		charConst.obj=new Obj(Obj.Con,"",Tab.charType);
		charConst.obj.setAdr(charConst.getValue());
	}
	public void visit(ConstBool boolConst) {
		boolConst.obj=new Obj(Obj.Con,"",BoolStruct);
		boolConst.obj.setAdr(boolConst.getValue()==true?1:0);
	}
	
	public void visit(DesignatorAssign desAsign) {
		if(desAsign.getDesignator().obj.getKind()==Obj.Var||desAsign.getDesignator().obj.getKind()==Obj.Fld) {
			if(desAsign.getDesignator().obj.getType().compatibleWith(desAsign.getExpr().struct)) {
				//sve ok
			}else {
				report_error("Error! Tipovi nisu kompatibilni "+desAsign.getDesignator().obj.getType().getKind()+desAsign.getExpr().struct.getKind(),desAsign);
			}
		}else if(desAsign.getDesignator().obj.getKind()==Obj.Elem){
			if(desAsign.getDesignator().obj.getType().compatibleWith(desAsign.getExpr().struct)) {
				//sve ok
			}else {
				report_error("Error! Tipovi nisu kompatibilni "+desAsign.getDesignator().obj.getType().getKind()+desAsign.getExpr().struct.getKind(),desAsign);
			}
		}else {
			report_error("Error! Designator "+desAsign.getDesignator().obj.getName()+" je pogresne vrste",desAsign);
		}
		
	}
	public void visit(DesignatorInc desInc) {
		if(desInc.getDesignator().obj.getKind()==Obj.Var||desInc.getDesignator().obj.getKind()==Obj.Elem||desInc.getDesignator().obj.getKind()==Obj.Fld) {
			if(desInc.getDesignator().obj.getType()==Tab.intType) {
				//sve ok
			}else {
				report_error("Error! Simbol nije tipa int",desInc);
			}
		}else {

			report_error("Error! Designator "+desInc.getDesignator().obj.getName()+" je pogresne vrste",desInc);
		}
	}
	public void visit(DesignatorDec desDec) {
		if(desDec.getDesignator().obj.getKind()==Obj.Var||desDec.getDesignator().obj.getKind()==Obj.Elem||desDec.getDesignator().obj.getKind()==Obj.Fld) {
			if(desDec.getDesignator().obj.getType()==Tab.intType) {
				//sve ok
			}else {
				report_error("Error! Simbol nije tipa int",desDec);
			}
		}else {

			report_error("Error! Designator "+desDec.getDesignator().obj.getName()+" je pogresne vrste",desDec);
		}
	}
	//!!!!!!!!!!!!!!!!!
	public void visit(DesignatorMethod desMeth) {
		if(desMeth.getDesignator().obj.getLevel()!=noActPars) {
			report_error("Error! Broj parametara se ne poklapa",desMeth);
		}else {
			noActPars=0;
		}
	}
	private boolean firstPass=true;
	private Stack<Integer> leviStek=new Stack<Integer>();
	private Stack<Integer> desniStek=new Stack<Integer>();
	public void visit(CountingOne cone) {
		int lev=leviStek.pop();
		lev++;
		leviStek.push(lev);
	}
	public void visit(CountingTwo ctwo) {
		int des=desniStek.pop();
		des++;
		desniStek.push(des);
	}
	Obj resobj=null;
	public void visit(DesignatorArrayInit desInit) {
		if(desInit.getExpr().struct!=Tab.intType) {
			report_error("Error! Broj elemenata niza mora biti tipa int",desInit);
		}else {
			if((firstPass)&&leviStek.peek()==desniStek.peek()) {
				desInit.obj=new Obj(Obj.Elem,desInit.getDesignator().obj.getName(),desInit.getDesignator().obj.getType().getElemType());
				resobj=desInit.obj;
				report_info("Alo "+desInit.obj.getType().getKind(),desInit);
				firstPass=false;
			}else
			if(leviStek.peek()>desniStek.peek()) {
				desInit.obj=new Obj(Obj.Elem,desInit.getDesignator().obj.getName(),desInit.getDesignator().obj.getType().getElemType());

				report_info("Alo "+desInit.obj.getType().getKind(),desInit);
			}else if(!firstPass){
				desInit.obj=resobj;
				leviStek.pop();
				desniStek.pop();
				report_info("Alo "+desInit.obj.getType().getKind(),desInit);
			}
		}
		report_info("LEva "+leviStek.peek()+" desna"+desniStek.peek(),desInit);
	}
	
	
	public void visit(DesignatorEnd desEnd) {
		desEnd.obj=Tab.find(desEnd.getIdent());
		report_info("bbbbbbb"+desEnd.obj.getType().getKind(),desEnd);
		if(desEnd.getParent() instanceof DesignatorArrayInit) {
			if(desEnd.obj.getType().getKind()!=Struct.Array) {
				report_error("Error! Promenljiva "+desEnd.obj.getName()+ " nije tipa array",desEnd);
			}else {
				firstPass=true;
				leviStek.push(0);
				desniStek.push(0);
			}
		}
		if(desEnd.obj==Tab.noObj) {
			report_error("Dato ime ne postoji",desEnd);
		}
	}
	
	
	
	public void visit(ActualParams actPars) {
		noActPars++;
	}
	public void visit(ActualParam actPars) {
		noActPars++;
	}
	public void visit(Actuals actPars) {
	}
}

