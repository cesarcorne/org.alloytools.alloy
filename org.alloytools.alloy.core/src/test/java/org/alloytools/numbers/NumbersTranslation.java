package org.alloytools.numbers;


import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import org.junit.Test;
import org.junit.Assert;
import org.junit.runners.JUnit4;

import java.util.LinkedList;
import java.util.List;

public class NumbersTranslation {

    /**
     * Given a number translates to Number8 Signatures which represents an integer of 8 bits
     * @param number
     * @param int8
     * @param boolMod
     * @return
     */
   private ExprList NewTranslator(int number, Module int8, Module boolMod){
       Sig bitNumber = int8.getAllSigs().get(0);
       StringBuilder reverseNumInBit = new StringBuilder(Integer.toBinaryString(number)).reverse();
       assert(reverseNumInBit.length() <= 8);
       reverseNumInBit.setLength(8);
       Sig boolTrue = int8.getAllReachableModules().get(2).getAllSigs().get(1);
       Sig boolFalse = int8.getAllReachableModules().get(2).getAllSigs().get(2);
       Expr e, leftExpr, rightExpr;
       List<Expr> exprs = new LinkedList<Expr>();
       ExprList finalExprList;
       for (int i = 0; i < reverseNumInBit.length(); i++) {
            leftExpr = bitNumber.getFieldDecls().get(i).expr;
            rightExpr = (reverseNumInBit.charAt(i) == '1') ?  boolTrue.decl.expr : boolFalse.decl.expr;
            e = leftExpr.equal(rightExpr);
            exprs.add(e);
       }
       finalExprList = ExprList.make(bitNumber.pos, bitNumber.closingBracket, ExprList.Op.AND, exprs);
       return finalExprList;
    }

    @Test
    public void checkTranslation(){
       // String filename = "src/main/resources/models/util/int8bits.als";
        String filename = "src/test/resources/num-test.als";
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        Module int8, boolMod;
        for (Module m : world.getAllReachableModules()){
            if (m.getModelName().equals("util/int8bits"))
                int8 = m;
            if (m.getModelName().equals("util/boolean"))
                boolMod = m;
        }
        int num = 22;
        ExprList result = NewTranslator(num,int8,boolMod);
        Assert.assertEquals(result.args.size(),8);
        System.out.println(result.toString());
    }

    public void exprToFact(){

    }

    @Test
    public void checkFact(){

    }

}