package aprove.verification.dpframework.Orders.SAT;

import java.util.*;
import java.util.logging.*;

import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class NewLPOEncoder extends AbstractPOEncoder {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SAT.LPOSEncoder");

    public NewLPOEncoder(FormulaFactory<None> formulaFactory, int restriction, AFSType afstype) {
        super(formulaFactory, false, false, true, false, true, true, restriction, afstype);
    }

    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {
        Poset<FunctionSymbol> poset = this.getPoset(knownTrue, afs);
        return new AfsOrder(afs, LPO.create(poset));
    }

}
