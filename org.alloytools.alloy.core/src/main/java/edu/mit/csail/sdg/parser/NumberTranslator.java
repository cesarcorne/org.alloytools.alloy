package edu.mit.csail.sdg.parser;

import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;

import java.util.LinkedList;
import java.util.List;

public class NumberTranslator {

    int bitRepresentation = 8;

    Module int8;

    Module world;

    public final Sig number8;

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

    /*public NumberTranslator(){
        String filename = "/Users/cesar/Documents/Doctorado/alloyarithmetic/org.alloytools.alloy/org.alloytools.alloy.core/src/main/resources/models/util/int8bits.als";
        //String filename = "src/main/resources/models/util/int8bits.als";
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        number8 = world.getAllSigs().get(0);
    }*/

    /**
     *
     * @return new Signature inherits Number8 signature
     */
    public Sig numberSigFactory(){
        Sig.PrimSig ghost = (Sig.PrimSig)int8.getAllSigs().get(0);
        Sig newSig = new Sig.PrimSig(signame + serial,(Sig.PrimSig) number8,Attr.SUBSIG,Attr.ONE);

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
        //ExprUnary prueba = (ExprUnary)ExprUnary.Op.NOOP.make(number8.pos, ExprVar.make(number8.pos, "this"));
        for (int i = 0; i < reverseNumInBit.length(); i++) {
            //leftField = result.getFieldDecls().get(i).expr;
            leftExpr = result.join((((Sig.PrimSig)result).parent.getFields().get(i)));
            //leftExpr = result.join(number8.getFields().get(i)).resolve(number8.type(), new JoinableList<ErrorWarning>());
            rightExpr = (reverseNumInBit.charAt(i) == '1') ?  boolTrue : boolFalse;
            //rightExpr = rightExpr.resolve(number8.type(), new JoinableList<ErrorWarning>());
            e = leftExpr.equal(rightExpr);
            //assert(e.errors.size() == 0);
            exprs.add(e);
        }
        //makes the final expr list
        finalExprList = (ExprList)ExprList.make(number8.pos, number8.closingBracket, ExprList.Op.AND, exprs).resolve_as_formula(new JoinableList<ErrorWarning>());
        result.addFact(finalExprList.resolve_as_formula(new JoinableList<ErrorWarning>()));
        LinkedList<ExprVar> parents = new LinkedList<ExprVar>();
        parents.add(ExprVar.make(number8.pos, number8.label));

        LinkedList<Decl> newDecls = new LinkedList<Decl>();
        for (Decl d: result.getFieldDecls())
               newDecls.add(d);
        ((CompModule)world).addSig(result.label, ExprVar.make(number8.pos, number8.label), parents, newDecls, finalExprList, Attr.ONE);
        return result;
    }


    public Sig newNumberSig(ExprList fact){
        Sig newSig = numberSigFactory();
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

    public void translateAllFacts(){
        NumberVisitor visitor = new NumberVisitor();
        for (Pair<String, Expr> fact : world.getAllFacts()){
            fact.b = fact.b.accept(visitor);
        }
    }

    public Expr translateOneExpr(Expr e){
        NumberVisitor visitor = new NumberVisitor();
        return e.accept(visitor);
    }

    /*public class NumberVisitor extends VisitReturn<Expr>{

        public NumberVisitor(){}

        @Override
        public Expr visit(ExprBinary x) throws Err {
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
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            List<Decl> newDecl = new LinkedList<Decl>();
            for (Decl d : x.decls){
                Decl nD = new Decl(d.isPrivate,d.disjoint,d.disjoint2,d.names,d.expr.accept(this));
                newDecl.add(nD);
            }
            ExprQt newExprQt = (ExprQt) x.op.make(x.pos,x.closingBracket,ConstList.make(newDecl),x.sub);
            return newExprQt.sub.accept(this);
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            //return numberSigFactory().oneOf();
            //if (x.type().is_int()) {
            //    if (x.op.equals(ExprUnary.Op.CAST2SIGINT)) {
            //        return x.sub.accept(this);
            //    } else {
            //        return x.sub.accept(this);
            //    }
            //}else
            //if (x.op.equals(ExprUnary.Op.NOOP)){

            //}
            return x.sub.accept(this);
            //return x.op.make(x.pos, x.sub.accept(this));
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            if (x.type().is_int())
                return ExprVar.make(x.pos,x.label,number8.type());
            else
                return x;
        }

        @Override
        public Expr visit(Sig x) throws Err {
            if (x.label.equals("Int"))
                return number8;
            Sig newSig = new Sig.PrimSig(x.label, x.attributes.get(0));
            List<Sig.Field> newFields = new LinkedList<Sig.Field>();
            for (Sig.Field f : x.getFields()){
                    newSig.addField(f.label, f.decl().expr.accept(this));
            }
            return newSig;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return x;
        }
    }*/

    public class NumberVisitor extends VisitReturn<Expr>{

        public NumberVisitor(){}

        @Override
        public Expr visit(ExprBinary x) throws Err {
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
            LinkedList<Expr> newArgs = new LinkedList<Expr>();
            for (Expr e : x.args){
                if (e.type().is_int())
                    newArgs.add(e.accept(this));
                else
                    newArgs.add(e);
            }
            return ExprCall.make(x.pos, x.pos, x.fun, ConstList.make(newArgs), x.extraWeight);
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            Sig newNum;
            if (x.type().is_int()){
                newNum = numberToFact(x.num);
                return newNum.typecheck_as_set();
            }else
                return x;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            return ExprITE.make(x.pos, x.cond.accept(this), x.left.accept(this), x.right.accept(this));
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            return  ExprLet.make(x.pos, (ExprVar) x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            List<Decl> newDecl = new LinkedList<Decl>();
            for (Decl d : x.decls){
                Decl nD = new Decl(d.isPrivate,d.disjoint,d.disjoint2,d.names,d.expr.accept(this));
                newDecl.add(nD);
            }

            if (x.sub instanceof ExprChoice){
                for (Expr e : ((ExprChoice) x.sub).choices){
                    List<Expr> newArgs = new LinkedList<Expr>();
                    if (!e.toString().startsWith("integer/") && e instanceof ExprBadCall){
                        for (Expr arg : ((ExprBadCall) e).args)
                            if (arg.type().is_int())
                                newArgs.add(arg.accept(this));
                            else
                                newArgs.add(arg);
                       Expr newCall = ExprCall.make(e.pos,e.closingBracket,((ExprBadCall) e).fun,newArgs,-1);
                        return (ExprQt) x.op.make(x.pos, x.closingBracket, ConstList.make(newDecl), newCall);
                    }

                }
            }

            return (ExprQt) x.op.make(x.pos,x.closingBracket,newDecl,x.sub.accept(this));
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            if (x.sub instanceof ExprConstant && x.sub.type.is_int()){
                Sig s = numberToFact(((ExprConstant)x.sub).num);
                x = (ExprUnary) ExprUnary.Op.NOOP.make(x.pos, s);
                return x.resolve_as_set(new LinkedList<ErrorWarning>());
            }
            if (x.type().is_int()) {
                x = (ExprUnary) ExprUnary.Op.NOOP.make(x.pos, number8);
            }
                // TODO aca sub tiene que ser una prim sig de number8 y type se tiene que pasar a number8
                //nueva expr unary que reemplace a x.
                //hacer un visitor que haga check de no exprchoice o badcall, luego replace

            return x.sub.accept(this);
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
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

    public class NumberCheck extends VisitReturn<Boolean>{

        NumberTranslator mainTranslator;
        public NumberCheck(NumberTranslator translator){
            mainTranslator = translator;
        }

        @Override
        public Boolean visit(ExprBinary x) throws Err {
            return true;
            //return x.left.accept(this) && x.right.accept(this);
        }

        @Override
        public Boolean visit(ExprList x) throws Err {
            /*Boolean value = true;
            for (Expr newArg : x.args)
                value = value && newArg.accept(this);
            return value;*/
            return true;
        }

        @Override
        public Boolean visit(ExprCall x) throws Err {
            /*Boolean value = true;
            for (Expr e : x.args){
                if (e.type().is_int())
                    value = value && false;
            }
            return value;*/
            return true;
        }

        @Override
        public Boolean visit(ExprConstant x) throws Err {
/*
            if (x.type().is_int()){
                return false;

            }else
                return true;*/
            return true;
        }

        @Override
        public Boolean visit(ExprITE x) throws Err {
           return true;// return x.cond.accept(this) && x.left.accept(this) && x.right.accept(this);
        }

        @Override
        public Boolean visit(ExprLet x) throws Err {
            return true;
            //return  x.var.accept(this) && x.expr.accept(this) && x.sub.accept(this));
        }

        @Override
        public Boolean visit(ExprQt x) throws Err {
            /*List<Decl> newDecl = new LinkedList<Decl>();
            for (Decl d : x.decls){
                Decl nD = new Decl(d.isPrivate,d.disjoint,d.disjoint2,d.names,d.expr.accept(this));
                newDecl.add(nD);
            }

            if (x.sub instanceof ExprChoice){
                for (Expr e : ((ExprChoice) x.sub).choices){
                    List<Expr> newArgs = new LinkedList<Expr>();
                    if (!e.toString().startsWith("integer/") && e instanceof ExprBadCall){
                        //ExprCall newCall;
                        for (Expr arg : ((ExprBadCall) e).args)
                            if (arg.type().is_int())
                                newArgs.add(arg.accept(this));
                            else
                                newArgs.add(arg);
                        Expr newCall = ExprCall.make(e.pos,e.closingBracket,((ExprBadCall) e).fun,newArgs,-1);
                        return (ExprQt) x.op.make(x.pos, x.closingBracket, ConstList.make(newDecl), newCall);
                    }

                }
            }

            return (ExprQt) x.op.make(x.pos,x.closingBracket,newDecl,x.sub.accept(this));*/
            return true;
        }

        @Override
        public Boolean visit(ExprUnary x) throws Err {
            if (x.sub instanceof ExprChoice){
                x.sub = ((ExprChoice)x.sub).resolveNumChoice(mainTranslator);
                return false;
            }
            else
                return true;
            /*if (x.type().is_int()) {
                x = (ExprUnary) ExprUnary.Op.NOOP.make(x.pos, number8);
            }*/
            // aca sub tiene que ser una prim sig de number8
            // y type se tiene que pasar a number8
            //nueva expr unary que reemplace a x.
            //hacer un visitor que haga check de no exprchoice o badcall, luego replace

            //return x.sub.accept(this);
        }

        @Override
        public Boolean visit(ExprVar x) throws Err {
            /*if (x.type().is_int())
                return ExprVar.make(x.pos,x.label,number8.type());
            else
                return x;*/
            return true;
        }

        @Override
        public Boolean visit(Sig x) throws Err {
            return true;
           // return x;
        }

        @Override
        public Boolean visit(Sig.Field x) throws Err {
            return true;
            //  return x;
        }
    }

    public boolean chechCalls(Expr e){
        NumberCheck chequer = new NumberCheck(this);
        return e.accept(chequer);
    }

}
