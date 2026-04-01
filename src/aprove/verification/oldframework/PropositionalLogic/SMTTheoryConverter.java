package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * interface for Converting propositions to SMTLIBIntCMP formulae C is the
 *
 * @author Christian Kuknat
 */
public interface SMTTheoryConverter<T_SRC, C extends SMTLIBVariable> extends
TheoryConverter<T_SRC, SMTLIBTheoryAtom> {

    public Map<String, C> getVariableMap();

    @Override
    public Formula<SMTLIBTheoryAtom> convert(T_SRC theoryProposition);

}