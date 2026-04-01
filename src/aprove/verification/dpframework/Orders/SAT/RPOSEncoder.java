package aprove.verification.dpframework.Orders.SAT;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;


public class RPOSEncoder extends AbstractPOEncoder {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SAT.RPOSEncoder");

    public RPOSEncoder(FormulaFactory<None> formulaFactory, int restriction, AFSType afstype) {
        super(formulaFactory, false, true, true, true, true, true, restriction, afstype);
    }

    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {
        if (Globals.DEBUG_NOWONDER) {
            Map<Variable<None>, Fact> factMap = this.factFactory.getFactMap();
            for (Variable<None> var : knownTrue) {
                RPOSEncoder.log.log(Level.FINEST, "{0}\n", factMap.get(var));
            }
        }
        Poset<FunctionSymbol> poset = this.getPoset(knownTrue, afs);
        StatusMap<FunctionSymbol> statusMap = this.getStatusMap(knownTrue, afs);
        return new AfsOrder(afs, RPOS.create(poset, statusMap));
    }

}
