package edu.mit.csail.sdg.parser;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.ast.*;

import java.util.LinkedList;
import java.util.List;

public class NumberTranslator {

    int bitRepresentation = 8;

    Module int8;

    private int serie = 0;
    private final String signame = "num";

    public Sig numberSigFactory(){
        Sig.PrimSig ghost = (Sig.PrimSig)int8.getAllSigs().get(0);
        Sig newSig = new Sig.PrimSig(signame + serie, ghost,Attr.ONE);
        serie++;
        return newSig;
    }

    public NumberTranslator(Module world){
        for (Module m : world.getAllReachableModules()){
            if (m.getModelName().equals("util/int8bits"))
                int8 = m;
        }
    }

    /**
     * Given a number makes the ExprList of its bit representation to add in a fact
     * @param number
     * @return
     */
    public ExprList numberToFact(int number){
        Sig bitNumber = int8.getAllSigs().get(0);
        StringBuilder reverseNumInBit = new StringBuilder(Integer.toBinaryString(number)).reverse();
        assert(reverseNumInBit.length() <= 8);
        reverseNumInBit.setLength(8);
        Sig boolTrue = int8.getAllReachableModules().get(2).getAllSigs().get(1);
        Sig boolFalse = int8.getAllReachableModules().get(2).getAllSigs().get(2);
        Expr e, leftField, rightExpr, leftSig;
        List<Expr> exprs = new LinkedList<Expr>();
        ExprList finalExprList;
        for (int i = 0; i < reverseNumInBit.length(); i++) {
            leftField = bitNumber.getFields().get(i);
            leftSig = bitNumber.join(leftField).resolve(bitNumber.type(), new JoinableList<ErrorWarning>());
            rightExpr = (reverseNumInBit.charAt(i) == '1') ?  boolTrue : boolFalse;
            rightExpr = rightExpr.resolve(bitNumber.type(), new JoinableList<ErrorWarning>());
            e = leftSig.equal(rightExpr);
            assert(e.errors.size() == 0);
            exprs.add(e);
        }
        //makes the final expr list
        finalExprList = ExprList.make(bitNumber.pos, bitNumber.closingBracket, ExprList.Op.AND, exprs);
        return finalExprList;
    }

    public Sig newNumberSig(ExprList fact){
        Sig ghost = int8.getAllSigs().get(0);
        Sig newSig = numberSigFactory();
        for (Sig.Field f : ghost.getFields())
            newSig.addDefinedField(f.pos, f.isPrivate, f.isMeta, f.label, f.resolve(f.type(), new JoinableList<ErrorWarning>()));
        newSig.addFact(fact);
        return newSig;
    }


    public void replacePred(Func f){
       NumberTranslator.NumberVisitor visitor = new NumberTranslator.NumberVisitor();
       for (Decl d : f.decls){
            if (d.expr.type().is_int()) {
                d = new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, d.expr.accept(visitor));
            }
       }

       Expr toReplace = f.getBody().accept(visitor);
       f.setBody(toReplace);

    }



    public class NumberVisitor extends VisitReturn<Expr>{

        public NumberVisitor(){}
        @Override
        public Expr visit(ExprBinary x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            if (x.fun.label.startsWith("integer/"))
                for (Func f : int8.getAllFunc())
                    if (f.label.contains(x.fun.label.substring(7,x.fun.label.length())))
                        return ExprCall.make(x.pos,x.pos,f,x.args,x.extraWeight);
            return x;
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            System.out.println("In visitor ExprUnary : " + x);
            //return numberSigFactory().oneOf();
            if (x.type().is_int())
                return int8.getAllSigs().get(0).oneOf();
            else
                return x.sub.accept(this);
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            System.out.println("In visitor ExprVar: " + x);
            //return numberSigFactory().oneOf();
            return int8.getAllSigs().get(0).oneOf();
        }

        @Override
        public Expr visit(Sig x) throws Err {
            return x;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return x;
        }
    }

}
