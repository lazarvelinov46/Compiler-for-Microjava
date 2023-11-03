package rs.ac.bg.etf.pp1;

import rs.ac.bg.etf.pp1.CounterVisitor.FormParamCounter;
import rs.ac.bg.etf.pp1.CounterVisitor.VarCounter;
import rs.ac.bg.etf.pp1.ast.*;

import java.util.List;
import java.util.ArrayList;
import java.util.Stack;

import rs.ac.bg.etf.pp1.*;
import rs.etf.pp1.mj.runtime.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;

enum RelopVisited {EQ,NEQ,GRE,GREQ,LE,LEQ}
enum AddopVisited {ADD,SUB}
enum MulopVisited {MUL,DIV,MOD}
enum ConstType {INT,CHAR,BOOL}

public class CodeGenerator extends VisitorAdaptor {
	
	private int varCount;
	private int paramCnt;
	private int breakNum=0;
	private Stack<Integer> leftMed=new Stack<Integer>();
	private Stack<Integer> rightMed=new Stack<Integer>();
	private int mainPc;
	private int constInt;
	private char constChar;
	private boolean startCount=false;
	private boolean readRows=false;
	private int rows;
	private class Jmp{
		public int rel;
		public int adr;
	}
	
	private int inWhile=0;
	private int exprCount=0;
	private int exprCount2=0;
	private boolean inMatrixCreate=false;
	private ArrayList<Jmp> andJumps=new ArrayList<Jmp>();
	private Stack<AddopVisited> addOps=new Stack<AddopVisited>();
	private Stack<MulopVisited> mulOps=new Stack<MulopVisited>();
	private ArrayList<Jmp> orJumps=new ArrayList<Jmp>();
	private ArrayList<Jmp> unresolvedIfJumps=new ArrayList<Jmp>();
	private Stack<ArrayList<Jmp>> nestedIfJumps=new Stack<ArrayList<Jmp>>();
	private Stack<ArrayList<Jmp>> nestedIfOrJumps=new Stack<ArrayList<Jmp>>();
	private Stack<ArrayList<Jmp>> nestedIfElseJumps=new Stack<ArrayList<Jmp>>();

	private Stack<ArrayList<Jmp>> nestedWhileJumps=new Stack<ArrayList<Jmp>>();
	private Stack<ArrayList<Jmp>> nestedWhileOrJumps=new Stack<ArrayList<Jmp>>();
	private Stack<Integer> mapAddress=new Stack<Integer>();
	private Stack<Integer> mapFixup=new Stack<Integer>(); 
	
	private Stack<Boolean> firstBrake=new Stack<Boolean>();
	private Stack<ArrayList<Integer>> breakAddress=new Stack<ArrayList<Integer>>();
	private Stack<ArrayList<Integer>> breakNums=new Stack<ArrayList<Integer>>();
	
	private Stack<Jmp> elseUnconditional=new Stack<Jmp>();
	private ArrayList<Integer> fixupAdrIf=new ArrayList<Integer>();
	private Stack<Integer> loopAddress=new Stack<Integer>();
	private ArrayList<Integer> loopFalse=new ArrayList<Integer>();
	private ArrayList<Integer> ifFalse=new ArrayList<Integer>();
	private ArrayList<Integer> ifTrue=new ArrayList<Integer>();
	private RelopVisited relopVisited;
	private AddopVisited addopVisited;
	private MulopVisited mulopVisited;
	private ConstType constType;

	
	public int getMainPc() {
		return mainPc;
	}
	//program
	
	public void visit(ProgName pname) {
		Tab.find("chr").setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		returnGeneral();
		Tab.find("ord").setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		returnGeneral();
		Tab.find("len").setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		Code.put(Code.arraylength);
		returnGeneral();
	}
	private void fcall(int offset) {
		Code.put(Code.call);
		Code.put2(offset);
		
	}
	//konstante
	
	public void visit (ConstNum cnum) {
		constType=ConstType.INT;
		constInt=cnum.getValue();
	}
	
	public void visit (ConstChar cchar) {
		constType=ConstType.CHAR;
		constChar=cchar.getValue();
	}
	
	public void visit (ConstBool cbool) {
		constType=ConstType.BOOL;
		constInt=cbool.getValue()==true?1:0;
	}
	
	//factor
	
	public void visit (FactorConst fconst) {
		if(constType==ConstType.INT||constType==ConstType.BOOL) {
			Code.loadConst(constInt);
		}else if(constType==ConstType.CHAR) {
			Code.loadConst(constChar);
		}
	}
	public void visit(FactorVar fVar) {
		Code.load(fVar.getDesignator().obj);
		if(cameFromArr==true) {
			cameFromArr=false;
			if(leftMed.size()>0) {
				leftMed.pop();
			}
			if(rightMed.size()>0) {
				rightMed.pop();
			}
		}
	}
	
	public void visit(FactorNew factArr) {
		Code.put(Code.newarray);
		if(factArr.getType().struct==Tab.charType) {
			Code.put(0);
		}else {
			Code.put(1);
		}
	}
	
	public void visit(FactorNewMat factMat) {
		//vidi kolko ima reda pa to puta len je pristup
		Code.put(Code.dup_x1);
		Code.put(Code.pop);
		Code.put(Code.newarray);
		if(factMat.getType().struct==Tab.charType) {
			Code.put(0);
		}else {
			Code.put(1);
		}
	}
	public void visit(Type type) {
		if(type.getParent()instanceof FactorNewMat) {
			readRows=true;
			inMatrixCreate=true;
		}
	}
	//method
	
	public void visit(MethodDeclar methDecl) {
		returnGeneral();
	}
	
	//statement
	
	public void visit(MatchedPrint matchedPrint) {
		if(matchedPrint.getExpr().struct==Tab.charType) {
			Code.put(Code.bprint);
		}else {
			Code.put(Code.print);
		}
	}
	
	public void visit(YesNum yn) {
		int num=yn.getN1();
		switch(num) {
		case 1:
			Code.put(Code.const_1);
			break;
		case 2:
			Code.put(Code.const_2);
			break;
		case 3:
			Code.put(Code.const_3);
			break;
		case 4:
			Code.put(Code.const_4);
			break;
		case 5:
			Code.put(Code.const_5);
			break;
		default:
			Code.loadConst(num);
		}
	}
	public void visit(NoNum nn) {
		Code.put(Code.const_5);
	}
	
	public void visit(Read rd) {
		if(rd.getDesignator().obj.getType()==Tab.charType) {
			Code.put(Code.bread);
		}else {
			Code.put(Code.read);
		}
		Code.store(rd.getDesignator().obj);
	}
	
	
	
	public void returnGeneral() {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	public void visit(MethodTypeName MethodTypeName) {
		if ("main".equalsIgnoreCase(MethodTypeName.getMethName())) {
			mainPc = Code.pc;
		}
		MethodTypeName.obj.setAdr(Code.pc);
		
		// Collect arguments and local variables.
		SyntaxNode methodNode = MethodTypeName.getParent();
		VarCounter varCnt = new VarCounter();
		methodNode.traverseTopDown(varCnt);
		FormParamCounter fpCnt = new FormParamCounter();
		methodNode.traverseTopDown(fpCnt);
		
		// Generate the entry.
		Code.put(Code.enter);
		Code.put(fpCnt.getCount());
		Code.put(varCnt.getCount() + fpCnt.getCount());
	}
	//designators
	public void visit(DesignatorAssign desAssign) {
		Obj obj=desAssign.getDesignator().obj;
		Code.store(obj);
		if(inMatrixCreate) {
			int loopAdr;
			int jmpAdr;
			Code.loadConst(0);
			loopAdr=Code.pc;
			Code.put(Code.dup);
			Code.load(obj);
			Code.put(Code.arraylength);
			jmpAdr=Code.pc+1;
			Code.putFalseJump(Code.lt,0);
			Code.put(Code.dup_x1);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.dup_x1);
			Code.put(Code.newarray);
			if(obj.getType().getElemType()==Tab.charType) {
				Code.put(0);
			}else {
				Code.put(1);
			}
			Code.load(obj);
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.put(Code.astore);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			Code.loadConst(1);
			Code.put(Code.add);
			Code.putJump(loopAdr);
			Code.fixup(jmpAdr);
			Code.put(Code.pop);
			Code.put(Code.pop);
			inMatrixCreate=false;
		}
		if(leftMed.size()>0) {
			leftMed.pop();
		}
		if(rightMed.size()>0) {
			rightMed.pop();
		}
		cameFromArr=false;
	}
	public void visit(DesignatorMethod desMethod) {
		int offset=desMethod.getDesignator().obj.getAdr()-Code.pc;
		fcall(offset);
		if(!isVoid) {
			Code.put(Code.pop);
		}
	}
	
	public void visit(CountingOne countOne) {
		int temp=leftMed.pop();
		temp++;
		leftMed.push(temp);
	}
	
	public void visit(CountingTwo countTwo) {
		int temp=rightMed.pop();
		temp++;
		rightMed.push(temp);
	}
	private boolean cameFromArr=false;
	public void visit(DesignatorArrayInit desArr) {
		if(leftMed.peek()==2&&rightMed.peek()==2) {
			Code.put(Code.dup_x2);
			Code.put(Code.pop);
			Code.load(desArr.getDesignator().obj);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			leftMed.pop();
			rightMed.pop();
			cameFromArr=false;
		}else {
			Code.load(desArr.getDesignator().obj);
			Code.put(Code.dup_x1);
			Code.put(Code.pop);
			cameFromArr=true;
		}

	}
	
	public void visit(DesignatorInc desInc) {
		Code.load(desInc.getDesignator().obj);
		Code.put(Code.const_1);
		Code.put(Code.add);
		Code.store(desInc.getDesignator().obj);
		exprCount=0;
		exprCount2=0;
	}
	
	public void visit(DesignatorDec desDec) {
		Code.load(desDec.getDesignator().obj);
		Code.put(Code.const_1);
		Code.put(Code.sub);
		Code.store(desDec.getDesignator().obj);
		exprCount=0;
		exprCount2=0;
	}
	
	/*
	@Override
	
	
	@Override
	public void visit(VarDecl VarDecl) {
		varCount++;
	}

	@Override
	public void visit(FormalParamDecl FormalParam) {
		paramCnt++;
	}	
	
	@Override
	public void visit(MethodDecl MethodDecl) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(ReturnExpr ReturnExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(ReturnNoExpr ReturnNoExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(Assignment Assignment) {
		Code.store(Assignment.getDesignator().obj);
	}
	
	@Override
	public void visit(Const Const) {
		Code.load(new Obj(Obj.Con, "$", Const.struct, Const.getN1(), 0));
	}
	
	@Override
	public void visit(Designator Designator) {
		SyntaxNode parent = Designator.getParent();
		if (Assignment.class != parent.getClass() && FuncCall.class != parent.getClass()) {
			Code.load(Designator.obj);
		}
	}
	
	@Override
	public void visit(FuncCall FuncCall) {
		Obj functionObj = FuncCall.getDesignator().obj;
		int offset = functionObj.getAdr() - Code.pc; 
		Code.put(Code.call);
		Code.put2(offset);
	}
	
	@Override
	public void visit(PrintStmt PrintStmt) {
		Code.put(Code.const_5);
		Code.put(Code.print);
	}
	
	@Override
	public void visit(AddExpr AddExpr) {
		Code.put(Code.add);
	}*/
	//petlje
	//while
	int noWhiles=0;
	public void visit(WhileStart whileStart) {
		inWhile=1;
		noWhiles++;
		loopAddress.push(Code.pc);
		firstBrake.push(true);
	}
	private boolean spajaj=false;
	public void visit(UnmatchedWhile unmatchedWhile) {
		Code.putJump(loopAddress.pop());
		noWhiles--;
		ArrayList<Jmp> temp=nestedWhileJumps.pop();
		for(int i=0;i<temp.size();i++) {
			Jmp jmp=temp.get(i);
			Code.fixup(jmp.adr);
		}
		if(firstBrake.pop()==false) {
			ArrayList<Integer> brkNums=breakNums.pop();
			ArrayList<Integer> breaks=breakAddress.pop();
			if(spajaj) {
				spajaj=false;
				ArrayList<Integer> brkNums2=breakNums.pop();
				ArrayList<Integer> breaks2=breakAddress.pop();
				for(int i=0;i<breaks2.size();i++) {
					brkNums.add(brkNums2.get(i));
					breaks.add(breaks2.get(i));
				}
			}
			ArrayList<Integer> brkNumsTemp=new ArrayList<Integer>();
			ArrayList<Integer> brksTemp=new ArrayList<Integer>();
			for(int i=0;i<breaks.size();i++) {
				if(brkNums.get(i)==1) {

					Code.fixup(breaks.get(i));
				}
				else {
					brkNumsTemp.add(brkNums.get(i)-1);
					brksTemp.add(breaks.get(i));
				}
			}
			if(brksTemp.size()>0) {

				spajaj=true;
				breakNums.push(brkNumsTemp);
				breakAddress.push(brksTemp);
			}
		}
		
	}
	private int skipAdr=-1;
	private int skipNo=0;
	public void visit(Skipping skip) {
		skipNo=skip.getValue();
		skipAdr=Code.pc+1;
		Code.putJump(0);
	}
	public void visit(SemiCounter semicnt) {
		if(skipAdr!=-1) {
			if(--skipNo==0) {
				Code.fixup(skipAdr);
				skipAdr=-1;
			}
		}
	}
	public void visit(MaxArr maxArr) {
		
	}
	public void visit(MatchedWhile matchedWhile) {
		Code.putJump(loopAddress.pop());
		noWhiles--;
		ArrayList<Jmp> temp=nestedWhileJumps.pop();
		for(int i=0;i<temp.size();i++) {
			Jmp jmp=temp.get(i);
			Code.fixup(jmp.adr);
		}
		if(firstBrake.pop()==false) {
			ArrayList<Integer> brkNums=breakNums.pop();
			ArrayList<Integer> breaks=breakAddress.pop();
			if(spajaj) {
				spajaj=false;
				ArrayList<Integer> brkNums2=breakNums.pop();
				ArrayList<Integer> breaks2=breakAddress.pop();
				for(int i=0;i<breaks2.size();i++) {
					brkNums.add(brkNums2.get(i));
					breaks.add(breaks2.get(i));
				}
			}
			ArrayList<Integer> brkNumsTemp=new ArrayList<Integer>();
			ArrayList<Integer> brksTemp=new ArrayList<Integer>();
			for(int i=0;i<breaks.size();i++) {
				if(brkNums.get(i)==1) {

					Code.fixup(breaks.get(i));
				}
				else {
					brkNumsTemp.add(brkNums.get(i)-1);
					brksTemp.add(breaks.get(i));
				}
			}
			/*
			 * ArrayList<Integer> brkNums2=breakNums.pop();
				ArrayList<Integer> breaks2=breakAddress.pop();
				for(int i=0;i<brksTemp.size();i++) {
					brkNums2.add(brkNumsTemp.get(i));
					breaks2.add(brksTemp.get(i));
				}
			 */
			if(brksTemp.size()>0) {
				
				spajaj=true;
				breakNums.push(brkNumsTemp);
				breakAddress.push(brksTemp);
			}
		}
	}
	public void visit(Break brk) {
		
		if(firstBrake.peek()) {
			firstBrake.pop();
			firstBrake.push(false);
			ArrayList<Integer> breaks=new ArrayList<Integer>();
			ArrayList<Integer> brkNums=new ArrayList<Integer>();
			breakNums.push(brkNums);
			breakAddress.push(breaks);
		}
		ArrayList<Integer> breaks=breakAddress.pop();
		ArrayList<Integer> brkNums=breakNums.pop();
		brkNums.add(1);
		breaks.add(Code.pc+1);
		Code.putJump(0);
		breakAddress.push(breaks);
		breakNums.push(brkNums);
	}
	public void visit(BreakNum breakNum) {
		int numBrk=breakNum.getValue();
		if(firstBrake.peek()) {
			firstBrake.pop();
			firstBrake.push(false);
			ArrayList<Integer> breaks=new ArrayList<Integer>();
			ArrayList<Integer> brkNums=new ArrayList<Integer>();
			breakNums.push(brkNums);
			breakAddress.push(breaks);
		}
		ArrayList<Integer> breaks=breakAddress.pop();
		ArrayList<Integer> brkNums=breakNums.pop();
		brkNums.add(numBrk);
		
		breaks.add(Code.pc+1);
		Code.putJump(0);
		breakAddress.push(breaks);
		breakNums.push(brkNums);
	}
	public void visit(Continue cnt) {
		Code.putJump(loopAddress.peek());
	}
	//map
	Obj mapDest;
	public void visit(MapStart mapStart) {
		Code.put(Code.newarray);
		if(mapDest.getType().getElemType()==Tab.charType) {
			Code.put(0);
		}else {
			Code.put(1);
		}
		Code.store(mapDest);
		Mapping mapParent=(Mapping)mapStart.getParent();
		Code.put(Code.const_);
		Code.put4(0);
		mapAddress.push(Code.pc);
		Code.put(Code.dup);
		Code.load(mapParent.getDesignator1().obj);
		Code.put(Code.arraylength);
		mapFixup.push(Code.pc+1);
		Code.putFalseJump(Code.lt,0);
		
	}
	public void visit(MapVar mapVar) {
		Mapping mapParent=(Mapping)mapVar.getParent();
		Code.put(Code.dup);
		Code.load(mapParent.getDesignator1().obj);
		Code.put(Code.dup_x1);
		Code.put(Code.pop);
		//proveri tipppppp
		//mora i ovo proveris
		if(mapVar.obj.getType()==Tab.charType) {

			Code.put(Code.baload);
		}else {
			Code.put(Code.aload);
		}
		Code.store(mapVar.obj);
	}
	public void visit(Mapping mapping) {
		Code.put(Code.dup2);
		Code.load(mapping.getDesignator().obj);
		Code.put(Code.dup_x2);
		Code.put(Code.pop);
		//mora proveris ovo
		if(mapping.getDesignator().obj.getType().getElemType()==Tab.charType) {

			Code.put(Code.bastore);
		}else {
			Code.put(Code.astore);
		}
		Code.put(Code.pop);
		//inc
		
		Code.loadConst(1);
		Code.put(Code.add);
		Code.putJump(mapAddress.pop());
		Code.fixup(mapFixup.pop());
		
	}
	//if
	public void visit(IfStart ifStart) {
		inWhile=0;
		ifFalse.add(0);
		if(ifStart.getParent() instanceof UnmatchedIfElse||ifStart.getParent() instanceof MatchedIf) {
			ifTrue.add(0);
		}
	}
	public void visit(Condition22 cond) {
		//adr1
		//ako nema and ili or poredi se sa 0
		/*
		if(orJumps.size()==0&&andJumps.size()==0) {
			Code.loadConst(0);
			ArrayList<Jmp> temp=new ArrayList<Jmp>();
			Jmp jmp=new Jmp();
			jmp.adr=Code.pc+1;
			Code.putFalseJump(Code.ne,0);
			temp.add(jmp);
			if(cond.getParent() instanceof MatchedIf || cond.getParent() instanceof UnmatchedIf || cond.getParent() instanceof UnmatchedIfElse) {
				nestedIfJumps.push(temp);	
			}else if(cond.getParent() instanceof UnmatchedWhile ||cond.getParent()instanceof MatchedWhile) {

				nestedWhileJumps.push(temp);
			}
		}else {*/
		/*
			
		if(orJumps.size()>0) {
			if(cond.getParent() instanceof MatchedIf || cond.getParent() instanceof UnmatchedIf || cond.getParent() instanceof UnmatchedIfElse) {
				ArrayList<Jmp> temp=new ArrayList<Jmp>();
				for(int i=0;i<orJumps.size();i++) {
					Jmp jmp=new Jmp();
					jmp.adr=orJumps.get(i).adr;
					jmp.rel=orJumps.get(i).rel;
					temp.add(jmp);
				}
				nestedIfOrJumps.push(temp);
			}
			else if(cond.getParent() instanceof UnmatchedWhile ||cond.getParent()instanceof MatchedWhile) {
				ArrayList<Jmp> temp=new ArrayList<Jmp>();
				for(int i=0;i<orJumps.size();i++) {
					Jmp jmp=new Jmp();
					jmp.adr=orJumps.get(i).adr;
					jmp.rel=orJumps.get(i).rel;
					temp.add(jmp);
				}
				nestedWhileOrJumps.push(temp);
			}
			orJumps.clear();
		}

			*/
		if(inWhile==0) {
			ArrayList<Jmp> temp=new ArrayList<Jmp>();
			for(int i=0;i<andJumps.size();i++) {
				Jmp jmp=andJumps.get(i);
				if(jmp.adr==-1) {
					Code.loadConst(0);
				}
				if(jmp.adr<=0) {

					jmp.adr=Code.pc+1;
					Code.putFalseJump(jmp.rel,0);
				}
				temp.add(jmp);
			}
			andJumps.clear();
			nestedIfJumps.push(temp);
			//stavi skokove u novu listu unresolved if jumps pa na kraj nadji adresu kraja i prodji kroz listu i onda fixap
		}else if(inWhile==1) {
			ArrayList<Jmp> temp=new ArrayList<Jmp>();
			for(int i=0;i<andJumps.size();i++) {
				Jmp jmp=andJumps.get(i);
				if(jmp.adr==-1) {
					Code.loadConst(0);
				}
				if(jmp.adr<=0) {

					jmp.adr=Code.pc+1;
					Code.putFalseJump(jmp.rel,0);
				}
				temp.add(jmp);
			}
			andJumps.clear();
			nestedWhileJumps.push(temp);
		}
			
			if(orJumps.size()>0) {
				for(int i=0;i<orJumps.size();i++) {
					Code.fixup(orJumps.get(i).adr);
					
				}
				orJumps.clear();
			}
		//}
		
	}
	public void visit(CondAnd condAnd) {
		if(inWhile==0) {
			for(int i=0;i<andJumps.size();i++) {
				if(andJumps.get(i).adr>0) {
					continue;
				}
				Jmp jmp=andJumps.get(i);
				if(jmp.adr==-1) {
					Code.loadConst(0);
				}
				andJumps.get(i).adr=Code.pc+1;
				Code.putFalseJump(jmp.rel,0);
			}
			//stavi skokove u novu listu unresolved if jumps pa na kraj nadji adresu kraja i prodji kroz listu i onda fixap
		}else if(inWhile==1) {
			for(int i=0;i<andJumps.size();i++) {
				if(andJumps.get(i).adr>0) {
					continue;
				}
				Jmp jmp=andJumps.get(i);
				if(jmp.adr==-1) {
					Code.loadConst(0);
				}
				andJumps.get(i).adr=Code.pc+1;
				Code.putFalseJump(jmp.rel,0);
			}
		}
	}
	public void visit(UnmatchedIf unIf) {
		ArrayList<Jmp> temp=nestedIfJumps.pop();
		for(int i=0;i<temp.size();i++) {
			Jmp jmp=temp.get(i);
			Code.fixup(jmp.adr);
		}
		/*
		ArrayList<Jmp> temp2=nestedIfOrJumps.pop();
		for(int i=0;i<temp2.size();i++) {
			Jmp jmp=temp2.get(i);
			Code.fixup(jmp.adr);
		}*/
	}
	public void visit(UnmatchedIfElse unIfElse) {
		Jmp jmp=elseUnconditional.pop();
		Code.fixup(jmp.adr);
	}
	public void visit(MatchedIf matIf) {

		Jmp jmp=elseUnconditional.pop();
		Code.fixup(jmp.adr);
	}
	//else
	public void visit(ElseStart elseStart) {
		Jmp unc=new Jmp();
		unc.adr=Code.pc+1;
		elseUnconditional.push(unc);
		Code.putJump(0);
		
		ArrayList<Jmp> temp=nestedIfJumps.pop();
		for(int i=0;i<temp.size();i++) {
			Jmp jmp=temp.get(i);
			Code.fixup(jmp.adr);
		}
	}
	//uslovi
	public void visit(CondOr condOr) {
		if(andJumps.size()>1) {
			for(int i=0;i<andJumps.size();i++) {
				Jmp jmp=andJumps.get(i);
				jmp.adr=Code.pc+1;
				Code.putFalseJump(jmp.rel,0);
				andJumps.set(i,jmp);
			}
			for(int i=0;i<andJumps.size();i++) {
				Code.fixup(andJumps.get(i).adr);
			}
			andJumps.clear();
		}else if(andJumps.size()==1) {
			Jmp jmp=andJumps.get(0);
			if(jmp.adr==-1) {
				Code.loadConst(0);
			}
			jmp.adr=Code.pc+1;
			Code.putFalseJump(Code.inverse[jmp.rel],0);
			orJumps.add(jmp);
			andJumps.clear();
		}
	}
	public void visit(EndCondFact endCondFact) {

		int jmpAdr=-1;
		Jmp jmp=new Jmp();
		jmp.rel=Code.ne;
		jmp.adr=jmpAdr;
		andJumps.add(jmp);
	}
	public void visit(CondFactRec condfactrec) {
		
		int rel;
		//{EQ,NEQ,GRE,GREQ,LE,LEQ}

		  //public static int eq=0, ne=1, lt=2, le=3, gt=4, ge=5;
		switch(relopVisited) {
		case EQ:
			rel=Code.eq;
			break;
		case NEQ:
			rel=Code.ne;
			break;
		case GRE:
			rel=Code.gt;
			break;
		case GREQ:
			rel=Code.ge;
			break;
		case LE:
			rel=Code.lt;
			break;
		case LEQ:
			rel=Code.le;
			break;
		default:
			rel=0;
			
		}
		int jmpAdr=0;
		Jmp jmp=new Jmp();
		jmp.rel=rel;
		jmp.adr=jmpAdr;
		andJumps.add(jmp);
	}
	//add
	private boolean isVoid=false;
	public void visit(FuncCall FuncCall) {
		int offset = FuncCall.getDesignator().obj.getAdr()-Code.pc;
		fcall(offset);
	}
	int cntMap=0;
	public void visit(DesignatorEnd desEnd) {
		if(desEnd.getParent() instanceof DesignatorArrayInit) {
			leftMed.push(0);
			rightMed.push(0);
		}else {
			cameFromArr=false;
		}
		if(desEnd.obj.getType()==Tab.noType) {
			isVoid=true;
		}else {
			isVoid=false;
		}
		if(desEnd.getParent() instanceof Mapping) {
			if(cntMap==1) {
				Code.load(desEnd.obj);
				Code.put(Code.arraylength);
				cntMap=0;
			}else {
				mapDest=desEnd.obj;
				cntMap++;
			}
		}
	}
	
	public void visit(AddExpr addexpr) {
		addopVisited=addOps.pop();
		switch (addopVisited) {
		case ADD:
			Code.put(Code.add);
			break;
		case SUB:
			Code.put(Code.sub);
			break;
		default:
			break;
		}
	}
	//mulop
	public void visit(TermNoMul tnm) {
		if(tnm.getParent()instanceof MinusTermExpr) {
			Code.put(Code.neg);
		}
	}
	public void visit(TermMul termMul) {
		if(termMul.getParent()instanceof MinusTermExpr) {
			Code.put(Code.neg);
		}
		mulopVisited=mulOps.pop();
		switch (mulopVisited) {
		case MUL:
			Code.put(Code.mul);
			break;
		case DIV:

			Code.put(Code.div);
			break;
		case MOD:

			Code.put(Code.rem);
			break;

		default:
			break;
		}
	}
	//relop
	
	public void visit(MinusTermExpr minustermexpr) {
	
	}
	
	
	//operators
	public void visit(AddopPlus addplu) {
		addOps.push(AddopVisited.ADD);
	}
	public void visit(AddopMinus addmin) {
		addOps.push(AddopVisited.SUB);
	}
	
	public void visit(MulopMul mulopmul) {
		mulOps.push(MulopVisited.MUL);
	}
	public void visit(MulopDiv mulopdiv) {
		mulOps.push(MulopVisited.DIV);
	}
	public void visit(MulopMod mulopmod) {
		mulOps.push(MulopVisited.MOD);
	}
	
	public void visit(RelopEq releq) {
		relopVisited=RelopVisited.EQ;
	}
	public void visit(RelopNeq releq) {
		relopVisited=RelopVisited.NEQ;
		
	}
	public void visit(RelopGre releq) {
		relopVisited=RelopVisited.GRE;
		
	}
	public void visit(RelopGreeq releq) {
		relopVisited=RelopVisited.GREQ;
		
	}
	public void visit(RelopLe releq) {
		relopVisited=RelopVisited.LE;
		
	}
	public void visit(RelopLeq releq) {
		relopVisited=RelopVisited.LEQ;
		
	}
}
