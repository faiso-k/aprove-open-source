package aprove.verification.dpframework.Orders.SAT;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Docu-guess (fuhs):
 * A SATEncoder allows you to encode rules as term constraints
 * for path orders. Here one encodes to formulas over partial
 * order constraints. For more details check the LPAR'06 paper
 * "SAT Solving for Argument Filterings" (Codish et al.) and
 * the FroCoS'07 "Proving Termination using Recursive Path
 * Orders and SAT Solving" (Schneider-Kamp et al.).
 */
public interface SATEncoder {

    public POFormula encode(Set<? extends GeneralizedRule> strict, Set<? extends GeneralizedRule> nonStrict, Abortion aborter) throws AbortionException;
    public POFormula encode(Set<? extends GeneralizedRule> strict, Map<? extends GeneralizedRule, QActiveCondition> activeNonStrict, boolean active, boolean allstrict, Abortion aborter) throws AbortionException;
    public POFormula encode(Set<? extends GeneralizedRule> strict, Abortion aborter) throws AbortionException;

    public Afs getAfs(Set<Variable<None>> knownTrue);

    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs);

    public boolean isAllowQuasi();

}
