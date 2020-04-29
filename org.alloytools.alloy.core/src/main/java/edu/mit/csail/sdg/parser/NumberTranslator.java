package edu.mit.csail.sdg.parser;

import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.ast.*;

import java.util.LinkedList;
import java.util.List;

public class NumberTranslator {

    int bitRepresentation = 8;

    /**
     * Given a number makes the ExprList of its bit representation to add in a fact
     * @param number
     * @param int8
     * @param boolMod
     * @return
     */
    private ExprList numberToFact(int number, Module int8, Module boolMod){
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

    public Sig newNumberSig(ExprList fact, Module int8){
        Sig ghost = int8.getAllSigs().get(0);
        Sig.PrimSig newSig = new Sig.PrimSig(ghost.label + "01", Attr.ONE);
        for (Sig.Field f : ghost.getFields())
            newSig.addDefinedField(f.pos, f.isPrivate, f.isMeta, f.label, f.resolve(f.type(), new JoinableList<ErrorWarning>()));
        newSig.addFact(fact);
        return newSig;
    }


}
