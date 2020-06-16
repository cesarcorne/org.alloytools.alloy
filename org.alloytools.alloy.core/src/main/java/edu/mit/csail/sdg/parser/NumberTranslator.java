package edu.mit.csail.sdg.parser;

import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;

import java.util.LinkedList;
import java.util.List;

public class NumberTranslator {

    int bitRepresentation = 8;

    Module int8;

    Module world;

    final Sig number8;

    private static int serial = 0;
    private final String signame = "num";

    /**
     * Construct a new translator.
     * TODO take other modules (16 bits, 32 bits, 64 bits)
     * @param world main module
     */
    public NumberTranslator(Module world){
        for (Module m : world.getAllReachableModules()){
            if (m.getModelName().equals("util/int8bits"))
                int8 = m;
        }
        number8 = int8.getAllSigs().get(0);
        this.world = world;
    }

    /**
     *
     * @return new Signature inherits Number8 signature
     */
    public Sig numberSigFactory(){
        Sig.PrimSig ghost = (Sig.PrimSig)int8.getAllSigs().get(0);
        Sig newSig = new Sig.PrimSig(signame + serial,(Sig.PrimSig) number8,Attr.ONE,Attr.SUBSIG);
        serial++;
        return newSig;
    }

    /**
     * Given a number it constructs a ExprList that represents it in binary and returns a signature that captures the representation as a Fact.
     * @param number the number to translate
     * @return a new Signature with a Fact capturing the bit representation of the number
     */
    public Sig numberToFact(int number){
        StringBuilder reverseNumInBit = new StringBuilder(Integer.toBinaryString(number)).reverse();
        assert(reverseNumInBit.length() <= 8);
        reverseNumInBit.setLength(8);
        Sig boolTrue = int8.getAllReachableModules().get(2).getAllSigs().get(1);
        Sig boolFalse = int8.getAllReachableModules().get(2).getAllSigs().get(2);
        Expr e, leftField, rightExpr, leftExpr;
        List<Expr> exprs = new LinkedList<Expr>();
        ExprList finalExprList;
        Sig result = numberSigFactory();
        for (int i = 0; i < reverseNumInBit.length(); i++) {
            leftField = number8.getFields().get(i);
            System.out.println("Left field : " + leftField.toString());
            leftExpr = result.join(leftField).resolve(number8.type(), new JoinableList<ErrorWarning>());
            System.out.println("Left Sig : " + result.toString());
            rightExpr = (reverseNumInBit.charAt(i) == '1') ?  boolTrue : boolFalse;
            System.out.println("Right Expr : " + rightExpr.toString());
            rightExpr = rightExpr.resolve(number8.type(), new JoinableList<ErrorWarning>());
            System.out.println("Right Expr 2 : " + rightExpr.toString());
            e = result.equal(rightExpr);
            System.out.println("E : " + e.toString());
            assert(e.errors.size() == 0);
            exprs.add(e);
        }
        //makes the final expr list
        finalExprList = ExprList.make(number8.pos, number8.closingBracket, ExprList.Op.AND, exprs);
        result.addFact(finalExprList);
        LinkedList<ExprVar> parents = new LinkedList<ExprVar>();
        parents.add(ExprVar.make(number8.pos, number8.label));

        LinkedList<Decl> newDecls = new LinkedList<Decl>();
        for (Decl d: result.getFieldDecls())
               newDecls.add(d);
        ((CompModule)world).addSig(result.label, ExprVar.make(number8.pos, number8.label), parents, newDecls, finalExprList, Attr.SUBSET);
        return result;
    }


    public Sig newNumberSig(ExprList fact){
        Sig newSig = numberSigFactory();
        //for (Sig.Field f : ghost.getFields())
        //    newSig.addDefinedField(f.pos, f.isPrivate, f.isMeta, f.label, f.resolve(f.type(), new JoinableList<ErrorWarning>()));
        System.out.println("Is subsig? : " + newSig.isSubsig);
        newSig.addFact(fact);
        return newSig;
    }

    /**
     * Given a function, changes de int type to NumberX of formal and actual parameters and also in the body
     * @param f
     */
    public void replacePred(Func f){
       NumberTranslator.NumberVisitor visitor = new NumberTranslator.NumberVisitor();
       Func oldF = f;
       List<Decl> newDecls = new LinkedList<Decl>();
       for (Expr param : f.params()){
           if (param.type().is_int()){
               Expr oldParam = param;
               Expr newParam = param.accept(visitor);
               f.params().remove(oldParam);
               f.params().add((ExprVar) newParam);
           }
       }
       for (Decl d : f.decls){
            if (d.expr.type().is_int()) {
                System.out.println("ver una decl : " +  d.expr.toString());
                Decl old = d;
                Decl toreplace = new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, d.expr.accept(visitor));
                newDecls.add(toreplace);
            }else{
                newDecls.add(d);
            }
       }
       f.replaceDecls(ConstList.make(newDecls));
       Expr toReplace = f.getBody().accept(visitor);
       toReplace.typecheck_as_formula();
       f.setBody(toReplace);
       //if (!f.decls.isEmpty())
       //    System.out.println("cambia el param? : " + f.decls.get(0).expr.type());
    }


    /**
     * Replace all int fields of a signature to NumberX
     * @param signature
     * @return
     */
    public Sig translateOneSig(Sig signature){
        Sig newSig = new Sig.PrimSig(signature.label, signature.attributes.get(0));
        NumberVisitor visitor = new NumberVisitor();
       for (Sig.Field f : signature.getFields()){
            newSig.addField(f.label, f.decl().expr.accept(visitor));
        }
        //System.out.println("new type ? : " + newSig.getFields().get(0).type());
        return newSig;
    }

    public void translateAllSigs(){
        for (Sig s : world.getAllSigs()){
            ((CompModule)world).replaceSig(s,translateOneSig(s));
        }
    }

    public void translateAllFuncs(){
        for (Func f : world.getAllFunc()){
            replacePred(f);
        }
    }

    public void translateAllAssertions(){
        NumberVisitor visitor = new NumberVisitor();
        for (Pair<String, Expr> assertion : world.getAllAssertions())
            assertion.b = assertion.b.accept(visitor);
    }

    public class NumberVisitor extends VisitReturn<Expr>{

        public NumberVisitor(){}

        @Override
        public Expr visit(ExprBinary x) throws Err {
            System.out.println("aca");
                return x.op.make(x.pos,x.closingBracket,x.left.accept(this),x.right.accept(this));

        }

        @Override
        public Expr visit(ExprList x) throws Err {
            LinkedList<Expr> newArgs = new LinkedList<Expr>();
            for (Expr newArg : x.args)
                newArgs.add(newArg.accept(this));
            ExprList nList = ExprList.make(x.pos,x.closingBracket,x.op,ConstList.make(newArgs));
            return nList;
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
                newNum = numberToFact(x.num);

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
            //if (x.op.equals(ExprUnary.Op.NOOP)){
             //   System.out.println("en noop" + x.toString());
            //}
            return x.sub.accept(this);
            //return x.op.make(x.pos, x.sub.accept(this));
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
           System.out.println("Sig type : " + x.type());
            if (x.label.equals("Int"))
                return number8;
            Sig newSig = new Sig.PrimSig(x.label, x.attributes.get(0));
            List<Sig.Field> newFields = new LinkedList<Sig.Field>();
            for (Sig.Field f : x.getFields()){
                    newSig.addField(f.label, f.decl().expr.accept(this));
            }

            //return x;
            return newSig;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            System.out.println("SigField type : " + x.type());
            //Sig newSig = new Sig(x.label, )

            return x;
        }
    }

}
