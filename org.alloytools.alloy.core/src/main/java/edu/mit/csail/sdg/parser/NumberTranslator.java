package edu.mit.csail.sdg.parser;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.ast.*;
import sun.awt.image.ImageWatched;

import java.util.LinkedList;
import java.util.List;

public class NumberTranslator {

    int bitRepresentation = 8;

    Module int8;

    Module world;

    final Sig number8;

    private int serial = 0;
    private final String signame = "num";

    public Sig numberSigFactory(){
        Sig.PrimSig ghost = (Sig.PrimSig)int8.getAllSigs().get(0);
        Sig newSig = new Sig.PrimSig(signame + serial, ghost,Attr.ONE);
        serial++;
        return newSig;
    }

    public NumberTranslator(Module world){
        for (Module m : world.getAllReachableModules()){
            if (m.getModelName().equals("util/int8bits"))
                int8 = m;
        }
        number8 = int8.getAllSigs().get(0);
        this.world = world;
    }

    /**
     * Given a number makes the ExprList of its bit representation to add in a fact
     * @param number
     * @return
     */
    public ExprList numberToFact(int number){
        StringBuilder reverseNumInBit = new StringBuilder(Integer.toBinaryString(number)).reverse();
        assert(reverseNumInBit.length() <= 8);
        reverseNumInBit.setLength(8);
        Sig boolTrue = int8.getAllReachableModules().get(2).getAllSigs().get(1);
        Sig boolFalse = int8.getAllReachableModules().get(2).getAllSigs().get(2);
        Expr e, leftField, rightExpr, leftSig;
        List<Expr> exprs = new LinkedList<Expr>();
        ExprList finalExprList;
        for (int i = 0; i < reverseNumInBit.length(); i++) {
            leftField = number8.getFields().get(i);
            leftSig = number8.join(leftField).resolve(number8.type(), new JoinableList<ErrorWarning>());
            rightExpr = (reverseNumInBit.charAt(i) == '1') ?  boolTrue : boolFalse;
            rightExpr = rightExpr.resolve(number8.type(), new JoinableList<ErrorWarning>());
            e = leftSig.equal(rightExpr);
            assert(e.errors.size() == 0);
            exprs.add(e);
        }
        //makes the final expr list
        finalExprList = ExprList.make(number8.pos, number8.closingBracket, ExprList.Op.AND, exprs);
        return finalExprList;
    }

    public Sig newNumberSig(ExprList fact){
        Sig ghost = number8;
        Sig newSig = numberSigFactory();
        for (Sig.Field f : ghost.getFields())
            newSig.addDefinedField(f.pos, f.isPrivate, f.isMeta, f.label, f.resolve(f.type(), new JoinableList<ErrorWarning>()));
        newSig.addFact(fact);
        return newSig;
    }


    public void replacePred(Func f){
       NumberTranslator.NumberVisitor visitor = new NumberTranslator.NumberVisitor();
       Func oldF = f;
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
            return x.op.make(x.pos,x.closingBracket,x.left.accept(this),x.left.accept(this));
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            LinkedList<Expr> newArgs = new LinkedList<Expr>();
            for (Expr newArg : x.args)
                newArgs.add(newArg.accept(this));
            ExprList nList = ExprList.make(x.pos,x.closingBracket,x.op,ConstList.make(newArgs));
            return x;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            if (x.fun.label.startsWith("integer/"))
                for (Func f : int8.getAllFunc())
                    if (f.label.contains(x.fun.label.substring(7,x.fun.label.length()))) {
                        LinkedList<Expr> newArgs = new LinkedList<Expr>();
                        for (Expr e : x.args){
                            if (e.type().is_int())
                                newArgs.add(e.accept(this));
                            else
                                newArgs.add(e);
                        }
                        return ExprCall.make(x.pos, x.pos, f, ConstList.make(newArgs), x.extraWeight);
                    }
            return x;
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            Sig newNum;
            if (x.type().is_int()){
                newNum = newNumberSig(numberToFact(x.num));
                world.getAllSigs().add(newNum);
                return newNum;
            }
            return x;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            return ExprITE.make(x.pos, x.cond.accept(this), x.left.accept(this), x.right.accept(this));
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            return  ExprLet.make(x.pos, (ExprVar) x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
            //return ExprLet.make(x.pos, x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            //LinkedList<Expr> newDecl
            List<Decl> newDecl = new LinkedList<Decl>();
            for (Decl d : x.decls){
                Decl nD = new Decl(d.isPrivate,d.disjoint,d.disjoint2,d.names,d.expr.accept(this));
                newDecl.add(nD);
            }
            //x.decls = ConstList.make(newDecl);
            ExprQt newExprQt = (ExprQt) x.op.make(x.pos,x.closingBracket,ConstList.make(newDecl),x.sub);
            return newExprQt.sub.accept(this);
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            //System.out.println("In visitor ExprUnary : " + x);
            //return numberSigFactory().oneOf();
            //if (x.type().is_int()) {
            //    if (x.op.equals(ExprUnary.Op.CAST2SIGINT)) {
            //        return x.sub.accept(this);
            //    } else {
            //        return x.sub.accept(this);
            //    }
            //}else
            return x.sub.accept(this);
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            //System.out.println("In visitor ExprVar: " + x);
            //return numberSigFactory().oneOf();
            if (x.type().is_int())
                return ExprVar.make(x.pos,x.label,number8.type());
            else
                return x;
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
