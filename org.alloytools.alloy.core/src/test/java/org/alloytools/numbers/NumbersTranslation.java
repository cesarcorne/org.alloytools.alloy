package org.alloytools.numbers;


import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.parser.NumberTranslator;
import org.junit.Test;
import org.junit.Assert;


public class NumbersTranslation {



    // String filename = "src/main/resources/models/util/int8bits.als";
    // String filename = "src/test/resources/example.als";
    String filename = "src/test/resources/num-test.als";
    Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
    int num = 22;


    @Test
    public void checkTranslation(){
        NumberTranslator translator = new NumberTranslator(world);
        ExprList result = translator.numberToFact(num);

        Assert.assertEquals(result.args.size(),8);
        System.out.println(result.toString());
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

        Assert.assertEquals(result, sig1.getFacts().get(0));
        Assert.assertEquals(sig1.getFacts(), translator.newNumberSig(result).getFacts());
        Sig record = translator.newNumberSig(result);
    }




    /*

     * Given a number translates to Number8 Signatures which represents an integer of 8 bits
     * @param number
     * @param int8
     * @param boolMod
     * @return

   private ExprList NewTranslator(int number, Module int8, Module boolMod){
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

*/

}
