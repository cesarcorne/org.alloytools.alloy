package edu.mit.csail.sdg.parser;

import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;

import java.lang.reflect.Field;
import java.util.*;

public class NumberTranslator {

    int bitRepresentation;

    Module int8;

    Module int16;

    Module int32;

    Module world;

    public final Sig number8;

    public final Sig number16;

    public final Sig number32;


    private static int serial = 0;
    private final String signame = "num";

    /**
     * Construct a new translator.
     * TODO take other modules (16 bits, 32 bits, 64 bits)
     * @param world main module
     */
    public NumberTranslator(Module world){
        this.bitRepresentation = 16;
        boolean uses8 = false, uses16 = false, uses32 = false;
        for (Module m : world.getAllReachableModules()){
            if (m.getModelName().equals("util/int8bits")) {
                int8 = m;
                uses8 = true;
            }
            if (m.getModelName().equals("util/int16bits")) {
                int16 = m;
                uses16 = true;
            }
            if (m.getModelName().equals("util/int32bits")) {
                int32 = m;
                uses32 = true;
            }
        }
        number8 = (uses8) ? int8.getAllSigs().get(0) : null;
        number16 = (uses16) ? int16.getAllSigs().get(0) : null;
        number32 = (uses32) ? int32.getAllSigs().get(0) : null;
        this.world = world;
    }

    public Sig actualRep(){
        switch (bitRepresentation){
            case 16 : return number16;
            case 32 : return number32;
            default: return number8;
        }
    }

    public Module actualModuleRep(){
        switch (bitRepresentation){
            case 16 : return int16;
            case 32 : return int32;
            default: return int8;
        }
    }

    /**
     *
     * @return new Signature inherits Number8 signature
     */
    public Sig numberSigFactory(){
        Sig.PrimSig ghost = (Sig.PrimSig)actualModuleRep().getAllSigs().get(0);
        Sig newSig = new Sig.PrimSig(signame + serial,(Sig.PrimSig) actualRep(),Attr.ONE);

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
        assert(reverseNumInBit.length() <= bitRepresentation);
        reverseNumInBit.setLength(bitRepresentation);
        Sig boolTrue = actualModuleRep().getAllReachableModules().get(2).getAllSigs().get(1);
        Sig boolFalse = actualModuleRep().getAllReachableModules().get(2).getAllSigs().get(2);
        Expr e, leftField, rightExpr, leftExpr;
        List<Expr> exprs = new LinkedList<Expr>();
        ExprList finalExprList;
        Sig result = numberSigFactory();
        //ExprUnary prueba = (ExprUnary)ExprUnary.Op.NOOP.make(number8.pos, ExprVar.make(number8.pos, "this"));
        for (int i = 0; i < reverseNumInBit.length(); i++) {
            //leftField = result.getFieldDecls().get(i).expr;
            //leftExpr = result.join((((Sig.PrimSig)result).parent.getFields().get(i)));
            leftExpr = result.join(((Sig.PrimSig)result).parent.getFields().get(i));
            //leftExpr = result.join(number8.getFields().get(i)).resolve(number8.type(), new JoinableList<ErrorWarning>());
            rightExpr = (reverseNumInBit.charAt(i) == '1') ?  boolTrue : boolFalse;
            //rightExpr = rightExpr.resolve(number8.type(), new JoinableList<ErrorWarning>());
            e = leftExpr.equal(rightExpr);
            //assert(e.errors.size() == 0);
            exprs.add(e);
        }
        //makes the final expr list
        finalExprList = (ExprList)ExprList.make(actualRep().pos, actualRep().closingBracket, ExprList.Op.AND, exprs).resolve_as_formula(new JoinableList<ErrorWarning>());
        result.addFact(finalExprList.resolve_as_formula(new JoinableList<ErrorWarning>()));
        LinkedList<ExprVar> parents = new LinkedList<ExprVar>();
        parents.add(ExprVar.make(actualRep().pos, actualRep().label));

        LinkedList<Decl> newDecls = new LinkedList<Decl>();
        for (Decl d: result.getFieldDecls())
               newDecls.add(d);
        //((CompModule)world).addSig(result.label, ExprVar.make(number8.pos, number8.label), parents, newDecls, finalExprList, Attr.ONE);
        addSigToModule(result);
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

    public void addSigToModule(Sig s) throws Err {
        addSigToModule_sigsField(s);
        addSigToModule_old2fieldsField(s);
        addSigToModule_sig2moduleField(s);
        addSigToModule_old2appendedfactsField(s);
    }

    private boolean setAccessibleStatus(Field f, boolean newValue) {
        boolean oldValue = f.isAccessible();
        f.setAccessible(newValue);
        return oldValue;
    }

    private void addSigToModule_sigsField(Sig sig) throws Err{
        Field sigsField = getField(CompModule.class, "sigs");
        try{
            boolean oldAccessibleStatus = setAccessibleStatus(sigsField, true);
            Map<String, Sig> sigs = (Map<String, Sig>) sigsField.get(world);
            if (sigs.containsKey(sig.toString())) {
                setAccessibleStatus(sigsField, oldAccessibleStatus);
                throw new IllegalAccessException("Sig to add (" + sig.toString() + ") already exists in module");
            }
            sigs.put(sig.toString(), sig);
            setAccessibleStatus(sigsField, oldAccessibleStatus);
        } catch (Exception e) {
            throw new ErrorFatal("An error occurred while trying to access sigs field");
        }
    }

    private static Field getField(Class< ? > from, String field) {
        for (Field f : from.getDeclaredFields()) {
            if (f.getName().compareTo(field) == 0)
                return f;
        }
        return null;
    }

    private void addSigToModule_old2fieldsField(Sig sig) throws Err {
        Field old2fieldsField = getField(CompModule.class, "old2fields");
        try {
            boolean oldAccessibleStatus = setAccessibleStatus(old2fieldsField, true);
            LinkedHashMap<Sig, List<Decl>> old2fields = (LinkedHashMap<Sig, List<Decl>>) old2fieldsField.get(world);
            if (old2fields.containsKey(sig)) {
                setAccessibleStatus(old2fieldsField, oldAccessibleStatus);
                throw new IllegalAccessException("Sig to add (" + sig.label + ") already exists in module");
            }
            old2fields.put(sig, sig.getFieldDecls().makeCopy());
            setAccessibleStatus(old2fieldsField, oldAccessibleStatus);
        } catch (IllegalAccessException e) {
            throw new ErrorFatal("An error occurred while trying to access old2fields field");
        }
    }

    private void addSigToModule_sig2moduleField(Sig sig) throws Err {
        Field sig2moduleField = getField(CompModule.class, "sig2module");
        try {
            boolean oldAccessibleStatus = setAccessibleStatus(sig2moduleField, true);
            HashMap<Sig, CompModule> sig2module = (HashMap<Sig, CompModule>) sig2moduleField.get(world);
            if (sig2module.containsKey(sig)) {
                setAccessibleStatus(sig2moduleField, oldAccessibleStatus);
                throw new IllegalAccessException("Sig to add (" + sig.label + ") already exists in module");
            }
            sig2module.put(sig, (CompModule) world);
            setAccessibleStatus(sig2moduleField, oldAccessibleStatus);
        } catch (IllegalAccessException e) {
            throw new ErrorFatal("An error occurred while trying to access sig2module field");
        }
    }

    private void addSigToModule_old2appendedfactsField(Sig sig) throws Err {
        Field old2appendedfactsField = getField(CompModule.class, "old2appendedfacts");
        try {
            boolean oldAccessibleStatus = setAccessibleStatus(old2appendedfactsField, true);
            LinkedHashMap<Sig,Expr> old2appendedfacts = (LinkedHashMap<Sig,Expr>) old2appendedfactsField.get(world);
            if (old2appendedfacts.containsKey(sig)) {
                setAccessibleStatus(old2appendedfactsField, oldAccessibleStatus);
                throw new IllegalAccessException("Sig to add (" + sig.label + ") already exists in module");
            }
            old2appendedfacts.put(sig, ExprConstant.TRUE);
            setAccessibleStatus(old2appendedfactsField, oldAccessibleStatus);
        } catch (IllegalAccessException e) {
            throw new ErrorFatal("An error occurred while trying to access old2appendedfacts field");
        }
    }

    public class NumberVisitor extends VisitReturn<Expr>{

        /*
        * TODO revisar resolveBadCall los arg, deben ser visitados siempre? o solo type = int?
        * */

        List<Decl> decls2Keep;
        List<ExprVar> exprs2Keep;

        public NumberVisitor(){
            decls2Keep = new LinkedList<Decl>();
            exprs2Keep = new LinkedList<ExprVar>();
        }

        private Expr getExprVar(ExprUnary e){
            while (e.sub instanceof ExprUnary){
                e = (ExprUnary) e.sub;
            }
            return (e.sub instanceof ExprVar) ? e.sub : e;
        }

        private boolean argInDeclList(Expr e) {
            if (e instanceof ExprUnary) {
                Expr eAsVar = getExprVar((ExprUnary) e);
                if (eAsVar instanceof ExprVar)
                    for (Decl d : this.decls2Keep)
                        for (ExprHasName eName : d.names)
                            if (eName instanceof ExprVar)
                                if (eName.label.equals(((ExprVar) eAsVar).label))
                                    return true;
            }
            return false;
        }

        private Expr getExprFromDeclList(Expr e){
            if (e instanceof ExprUnary) {
                Expr eAsVar = getExprVar((ExprUnary) e);
                if (eAsVar instanceof ExprVar)
                    for (Decl d : this.decls2Keep)
                        for (ExprHasName eName : d.names)
                            if (eName instanceof ExprVar)
                                if (eName.label.equals(((ExprVar) eAsVar).label))
                                    return eName;
            }
            return null;
        }

        private Expr resolveDeclsInBadCall(ExprBadCall x) {
            List<Expr> newArgs = new LinkedList<Expr>();
            for (Expr e : x.args)
                newArgs.add(argInDeclList(e) ? getExprFromDeclList(e) : e);
            return ExprBadCall.make(x.pos, x.closingBracket, x.fun, ConstList.make(newArgs), x.extraWeight);
        }

        private boolean argInExprList(Expr e){
            for (ExprVar var : this.exprs2Keep)
                if (e instanceof ExprUnary) {
                    Expr eAsVar = getExprVar((ExprUnary) e);
                    if (eAsVar instanceof ExprVar && ((ExprVar) eAsVar).label.equals(var.label))
                        return true;
                }
            return false;
        }

        private Expr getArgFromList(Expr e){
            for (ExprVar var : this.exprs2Keep) {
                if (e instanceof ExprUnary) {
                    Expr eAsVar = getExprVar((ExprUnary) e);
                    if (eAsVar instanceof ExprVar && ((ExprVar) eAsVar).label.equals(var.label))
                        return var;
                }
            }
            return null;
        }

        private Expr resolveExprInBadCAll(ExprBadCall x){
            List<Expr> newArgs = new LinkedList<Expr>();
            for (Expr e : x.args)
                newArgs.add((argInExprList(e)) ? getArgFromList(e) : e);
            return ExprBadCall.make(x.pos, x.closingBracket, x.fun, ConstList.make(newArgs), x.extraWeight);
        }

        public Expr resolveBadCall(ExprBadCall x){
            if (! decls2Keep.isEmpty())
                x = (ExprBadCall) resolveDeclsInBadCall(x);
            if (! exprs2Keep.isEmpty())
                x = (ExprBadCall) resolveExprInBadCAll(x);
            List<Expr> newArgs = new LinkedList<Expr>();
            for (Expr arg : x.args)
                newArgs.add(arg instanceof ExprChoice ? selectInChoice((ExprChoice)arg) : arg.accept(this));
            return ExprCall.make(x.pos, x.pos, x.fun, ConstList.make(newArgs), x.extraWeight);
        }

        public Expr selectInChoice(ExprChoice eBad){
            for (Expr chosen : eBad.choices){
                if (!chosen.toString().startsWith("integer/"))
                    return (chosen instanceof ExprBadCall) ? resolveBadCall((ExprBadCall) chosen) : chosen.accept(this);
            }
            return eBad;
        }


        @Override
        public Expr visit(ExprBinary x) throws Err {
            Expr left = (x.left instanceof ExprChoice) ? selectInChoice((ExprChoice) x.left) : x.left.accept(this);
            Expr right = (x.right instanceof ExprChoice) ? selectInChoice((ExprChoice) x.right) : x.right.accept(this);
            return x.op.make(x.pos,x.closingBracket,left,right);
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            LinkedList<Expr> newArgs = new LinkedList<Expr>();
            for (Expr newArg : x.args)
                newArgs.add(newArg instanceof ExprChoice ? selectInChoice((ExprChoice) newArg) : newArg.accept(this));

            ExprList nList = ExprList.make(x.pos,x.closingBracket,x.op,ConstList.make(newArgs));
            return nList;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            LinkedList<Expr> newArgs = new LinkedList<Expr>();
            for (Expr e : x.args){
                if (e.type().is_int()) {
                    newArgs.add(e.accept(this));
                }else
                    if (e instanceof ExprChoice)
                        newArgs.add(selectInChoice((ExprChoice) e));
                    else
                        newArgs.add(e.accept(this));
            }
                return ExprCall.make(x.pos, x.pos, x.fun, ConstList.make(newArgs), x.extraWeight);
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            Sig newNum;
            if (x.type().is_int()) {
                newNum = numberToFact(x.num);
                return newNum.typecheck_as_set();
            } else
                return x;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            Expr cond = (x.cond instanceof ExprChoice) ? selectInChoice((ExprChoice) x.cond) : x.cond.accept(this);
            Expr left = (x.cond instanceof ExprChoice) ? selectInChoice((ExprChoice) x.left) : x.left.accept(this);
            Expr right = (x.cond instanceof ExprChoice) ? selectInChoice((ExprChoice) x.right) : x.cond.accept(this);
            return ExprITE.make(x.pos, cond, left, right);
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            Expr var = x.var.accept(this);
            Expr expr = x.expr.accept(this);
            this.exprs2Keep.add((ExprVar)var);
            Expr sub = (x.sub instanceof ExprChoice) ? selectInChoice((ExprChoice) x.sub) : x.sub.accept(this);
            this.exprs2Keep.remove(var);
            return ExprLet.make(x.pos, (ExprVar) var, expr, sub);
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            List<Decl> newDecls = new LinkedList<Decl>();
            for (Decl d : x.decls){
                if (d.expr.type().is_int()){
                    Expr e = d.expr.accept(this);
                    List<ExprHasName> newNames = new LinkedList<ExprHasName>();
                    for (ExprHasName n : d.names){
                        if (n instanceof ExprVar)
                            newNames.add(ExprVar.make(n.pos, n.label, actualRep().type));
                        else
                            newNames.add(n);
                        }
                    newDecls.add(new Decl(d.isPrivate,d.disjoint,d.disjoint2, ConstList.make(newNames),e));
                }else
                    newDecls.add(d);
            }
            this.decls2Keep.addAll(newDecls);
            Expr newSub = (x.sub instanceof ExprChoice) ? selectInChoice((ExprChoice) x.sub) : x.sub.accept(this);
            this.decls2Keep.removeAll(newDecls);
            return x.op.make(x.pos, x.closingBracket, newDecls, newSub);
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            if (x.sub instanceof ExprConstant && x.sub.type.is_int()){
                Sig s = numberToFact(((ExprConstant)x.sub).num);
                x = (ExprUnary) ExprUnary.Op.NOOP.make(x.pos, s);
                return x.resolve_as_set(new LinkedList<ErrorWarning>());
            }else
                if (x.type().is_int()) {
                    return (ExprUnary) x.op.make(x.pos, actualRep());
                }else
                    if (x.sub instanceof ExprChoice){
                        x.sub = selectInChoice((ExprChoice)x.sub);
                    }else
                        if (x.sub instanceof ExprBadCall){
                            x.sub = resolveBadCall((ExprBadCall)x.sub);
                        }else
                            x.sub = x.sub.accept(this);
                return x.op.make(x.pos, x.sub);
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            if (x.type().is_int())
                return ExprVar.make(x.pos,x.label,actualRep().type());
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