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

public class QRPOSEncoder extends AbstractPOEncoder {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SAT.QRPOSEncoder");

    public QRPOSEncoder(FormulaFactory<None> formulaFactory, int restriction, AFSType afstype) {
        super(formulaFactory, true, true, true, true, true, true, restriction, afstype);
    }

    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {
        if (Globals.DEBUG_NOWONDER) {
            Map<Variable<None>, Fact> factMap = this.factFactory.getFactMap();
            for (Variable<None> var : knownTrue) {
                QRPOSEncoder.log.log(Level.FINEST, "{0}\n", factMap.get(var));
            }
        }
        Qoset<FunctionSymbol> qoset = this.getQoset(knownTrue, afs);
        StatusMap<FunctionSymbol> statusMap = this.getStatusMap(knownTrue, afs);
        if (Globals.DEBUG_NOWONDER) {
            System.out.println("=======================");
            System.out.println(QRPOS.create(qoset, statusMap));
            System.out.println(afs);
            System.out.println("=======================");
        }
        return new AfsOrder(afs, QRPOS.create(qoset, statusMap));
    }

}
