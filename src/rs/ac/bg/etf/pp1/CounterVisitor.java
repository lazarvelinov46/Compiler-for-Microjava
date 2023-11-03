package rs.ac.bg.etf.pp1;

import rs.ac.bg.etf.pp1.ast.FormalParamDecl;
import rs.ac.bg.etf.pp1.ast.FormalParamVar;
import rs.ac.bg.etf.pp1.ast.FormalParamArray;
import rs.ac.bg.etf.pp1.ast.FormalParamMatrix;
import rs.ac.bg.etf.pp1.ast.VarDecl;
import rs.ac.bg.etf.pp1.ast.VarDeclar;
import rs.ac.bg.etf.pp1.ast.VisitorAdaptor;

public class CounterVisitor extends VisitorAdaptor {
	
	protected int count;
	
	public int getCount() {
		return count;
	}
	
	public static class FormParamCounter extends CounterVisitor {

		@Override
		public void visit(FormalParamVar formParamDecl1) {
			count++;
		}		
		@Override
		public void visit(FormalParamArray formParamDecl1) {
			count++;
		}		
		@Override
		public void visit(FormalParamMatrix formParamDecl1) {
			count++;
		}		
	}
	
	public static class VarCounter extends CounterVisitor {		
		@Override
		public void visit(VarDeclar VarDecl) {
			count++;
		}
	}
}
