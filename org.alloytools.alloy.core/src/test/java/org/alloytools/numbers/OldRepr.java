package org.alloytools.numbers;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import org.junit.Assert;
import org.junit.Test;

public class OldRepr {


    @Test
    public void checkOldInts(){
        String filename = "src/test/resources/oldIntsSig.als";
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        for (Sig s : world.getAllSigs())
            for (Sig.Field f : s.getFields())
                Assert.assertEquals("{this/A->this/Number8}", f.type().toString());
    }
}
