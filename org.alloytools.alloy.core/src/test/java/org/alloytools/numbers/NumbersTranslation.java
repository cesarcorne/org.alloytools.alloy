package org.alloytools.numbers;


import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.parser.NumberTranslator;
import org.junit.Test;
import org.junit.Assert;

import java.util.LinkedList;
import java.util.List;


public class NumbersTranslation {



    // String filename = "src/main/resources/models/util/int8bits.als";
    // String filename = "src/test/resources/example.als";
    String filename = "src/test/resources/num-test.als";
    Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
    int num = 22;
    //Module int8 = ;
    public class CountInt extends VisitReturn<Integer>{

        public CountInt(){}

        @Override
        public Integer visit(ExprBinary x) throws Err {
            return x.left.accept(this) + x.right.accept(this);
            //return x.op.make(x.pos,x.closingBracket,x.left.accept(this),x.left.accept(this));
        }

        @Override
        public Integer visit(ExprList x) throws Err {
            Integer result = 0;
            for (Expr newArg : x.args)
                result += newArg.accept(this);
            return result;
        }

        @Override
        public Integer visit(ExprCall x) throws Err {
            Module int8 = null;
            for (Module m : world.getAllReachableModules()){
                if (m.getModelName().equals("util/int8bits"))
                    int8 = m;
            }
            Integer result = 0;
            if (x.fun.label.startsWith("integer/"))
                for (Func f : int8.getAllFunc())
                    if (f.label.contains(x.fun.label.substring(7,x.fun.label.length()))) {
                        LinkedList<Expr> newArgs = new LinkedList<Expr>();
                        for (Expr e : x.args){
                            if (e.type().is_int())
                                result += 1;
                        }
                        return result;
                    }
            return result;
        }

        @Override
        public Integer visit(ExprConstant x) throws Err {
            Integer result;
            Sig newNum;
            if (x.type().is_int()){
                return 1;
            }
            return 0;
        }

        @Override
        public Integer visit(ExprITE x) throws Err {
            return x.cond.accept(this) + x.left.accept(this) + x.right.accept(this);
            //return ExprITE.make(x.pos, x.cond.accept(this), x.left.accept(this), x.right.accept(this));
        }

        @Override
        public Integer visit(ExprLet x) throws Err {
            return x.var.accept(this) + x.expr.accept(this) + x.sub.accept(this);
            //return  ExprLet.make(x.pos, (ExprVar) x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
            //return ExprLet.make(x.pos, x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
        }

        @Override
        public Integer visit(ExprQt x) throws Err {
            //LinkedList<Expr> newDecl
            Integer result=0;
            List<Decl> newDecl = new LinkedList<Decl>();
            for (Decl d : x.decls){
                result += d.expr.accept(this);
            }
            return result + x.sub.accept(this);
        }

        @Override
        public Integer visit(ExprUnary x) throws Err {
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
        public Integer visit(ExprVar x) throws Err {
            //System.out.println("In visitor ExprVar: " + x);
            //return numberSigFactory().oneOf();
            if (x.type().is_int())
                return 1;
            else
                return 0;
        }

        @Override
        public Integer visit(Sig x) throws Err {

            return -1;
        }

        @Override
        public Integer visit(Sig.Field x) throws Err {
            return -1;
        }
    }

    public class CountNum8 extends VisitReturn<Integer>{

        public CountNum8(){}

        @Override
        public Integer visit(ExprBinary x) throws Err {
            return x.left.accept(this) + x.right.accept(this);
            //return x.op.make(x.pos,x.closingBracket,x.left.accept(this),x.left.accept(this));
        }

        @Override
        public Integer visit(ExprList x) throws Err {
            Integer result = 0;
            for (Expr newArg : x.args)
                result += newArg.accept(this);
            return result;
        }

        @Override
        public Integer visit(ExprCall x) throws Err {
            Module int8 = null;
            for (Module m : world.getAllReachableModules()){
                if (m.getModelName().equals("util/int8bits")) {
                    int8 = m;
                    break;
                }
            }
            Integer result = 0;
            if (x.fun.label.startsWith("int8bits/"))
                for (Func f : int8.getAllFunc())
                    if (f.label.contains(x.fun.label.substring(9,x.fun.label.length()))) {
                        LinkedList<Expr> newArgs = new LinkedList<Expr>();
                        for (Expr e : x.args){
                            if (e.type().toString().equals("{int8bits/Number8}") || e.type().toString().startsWith("{num"))
                                result += 1;
                        }
                        return result;
                    }
            return result;
        }

        @Override
        public Integer visit(ExprConstant x) throws Err {
            Integer result;
            Sig newNum;
            if (x.type().toString().equals("{int8bits/Number8}")){
                return 1;
            }
            return 0;
        }

        @Override
        public Integer visit(ExprITE x) throws Err {
            return x.cond.accept(this) + x.left.accept(this) + x.right.accept(this);
            //return ExprITE.make(x.pos, x.cond.accept(this), x.left.accept(this), x.right.accept(this));
        }

        @Override
        public Integer visit(ExprLet x) throws Err {
            return x.var.accept(this) + x.expr.accept(this) + x.sub.accept(this);
            //return  ExprLet.make(x.pos, (ExprVar) x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
            //return ExprLet.make(x.pos, x.var.accept(this), x.expr.accept(this), x.sub.accept(this));
        }

        @Override
        public Integer visit(ExprQt x) throws Err {
            //LinkedList<Expr> newDecl
            Integer result=0;
            List<Decl> newDecl = new LinkedList<Decl>();
            for (Decl d : x.decls){
                result += d.expr.accept(this);
            }
            return result + x.sub.accept(this);
        }

        @Override
        public Integer visit(ExprUnary x) throws Err {
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
        public Integer visit(ExprVar x) throws Err {
            //System.out.println("In visitor ExprVar: " + x);
            //return numberSigFactory().oneOf();
            if (x.type().toString().equals("{int8bits/Number8}"))
                return 1;
            else
                return 0;
        }

        @Override
        public Integer visit(Sig x) throws Err {
            if (x.label.startsWith("num"))
                return 1;
            else
                return 0;
        }

        @Override
        public Integer visit(Sig.Field x) throws Err {
            if (x.label.startsWith("num"))
                return 1;
            else return 0;
        }
    }

    @Test
    public void checkTranslation(){
        NumberTranslator translator = new NumberTranslator(world);
        ExprList result = translator.numberToFact(num);

        Assert.assertEquals(result.args.size(),8);
        System.out.println(result.toString());
        System.out.println("Test 1");
        for (Func f : world.getAllFunc())
            translator.replacePred(f);
    }


    @Test
    public void checkNewSig(){
        Module moduleInt = null;
        for (Module m : world.getAllReachableModules()) {
            if (m.getModelName().equals("util/int8bits"))
                moduleInt = m;
        }
        NumberTranslator translator = new NumberTranslator(world);
        ExprList result = translator.numberToFact(22);
        Sig sig1 = translator.numberSigFactory();
        sig1.addFact(result);
        System.out.println("Test 2");

        Assert.assertEquals(result, sig1.getFacts().get(0));
        Assert.assertEquals(sig1.getFacts(), translator.newNumberSig(result).getFacts());
        Sig record = translator.newNumberSig(result);
    }

    /**
     * IntegrationTest1 reaches coverage of ExprList, ExprCall, ExprConst, ExprUnary, ExprVar and Sig
     */
    @Test
    public void IntegrationTest1(){

        String filename = "src/test/resources/ExprBin-test.als";
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        Func pred = world.getAllFunc().get(0);
        CountInt countViz = new CountInt();
        Integer result = pred.getBody().accept(countViz);
        System.out.println("Test 3");

        NumberTranslator translator = new NumberTranslator(world);
        translator.replacePred(pred);

        CountNum8 countNum8Viz = new CountNum8();
        Integer newResult = pred.getBody().accept(countNum8Viz);

        Assert.assertEquals(result, newResult);
    }

    @Test
    public void IntegrationTest2(){
        String filename = "src/test/resources/sig-test.als";
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        System.out.println("Test 4");

        System.out.println(world.getAllSigs().get(0).getFields().get(0).type());
        NumberTranslator translator = new NumberTranslator(world);
        System.out.println("prueba translator: " + translator.translateSigs(world.getAllSigs().get(0)).getFields().get(0).type());
        world.replaceSig(world.getAllSigs().get(0),translator.translateSigs(world.getAllSigs().get(0)));
        System.out.println("a ver-> : " + world.getAllSigs().get(0).getFields().get(0).type());

    }

    @Test
    public void JoinTest(){
        String filename = "src/test/resources/Join-test.als";
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);

        System.out.println(world.getAllSigs().get(0).getFields().get(0).type());
        NumberTranslator translator = new NumberTranslator(world);
        System.out.println("prueba translator: " + translator.translateSigs(world.getAllSigs().get(0)).getFields().get(0).type());
        world.replaceSig(world.getAllSigs().get(0),translator.translateSigs(world.getAllSigs().get(0)));
        System.out.println("a ver-> : " + world.getAllSigs().get(0).getFields().get(0).type());

        System.out.println("Test 5");

        Func pred = world.getAllFunc().get(0);
        CountInt countViz = new CountInt();
        Integer result = pred.getBody().accept(countViz);

        NumberTranslator translator2 = new NumberTranslator(world);
        translator2.replacePred(pred);

        CountNum8 countNum8Viz = new CountNum8();
        Integer newResult = pred.getBody().accept(countNum8Viz);

        Assert.assertEquals(result, newResult);
    }

    

}
