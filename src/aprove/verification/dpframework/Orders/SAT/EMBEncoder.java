package aprove.verification.dpframework.Orders.SAT;

import java.util.*;
import java.util.logging.*;

import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class EMBEncoder extends AbstractPOEncoder {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SAT.EMBEncoder");

    public EMBEncoder(FormulaFactory<None> formulaFactory, int restriction, AFSType afstype) {
        super(formulaFactory, false, false, false, false, false, false, restriction, afstype);
    }

    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {
        return new AfsOrder(afs, EMB.create());
    }

}
