package aprove.input.Programs.pushdownSMT;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import immutables.*;

/**
 * Representation of integer transition systems with recursion.
 *
 * @author Marc Brockschmidt
 */
public class SMTPushdownAutomaton extends DefaultBasicObligation {
    /** Constraints on initial states. */
    private final PushdownInitInformation init;
    /** Intra-procedural transitions. */
    private final ImmutableCollection<PushdownProcedureInformation> procedures;
    /** Calls between procedures. */
    private final ImmutableCollection<PushdownCallInformation> calls;
    /** Returns from procedure calls. */
    private final ImmutableCollection<PushdownReturnInformation> returns;

    public SMTPushdownAutomaton(
            final PushdownInitInformation i,
            final Collection<PushdownProcedureInformation> ps,
            final Collection<PushdownCallInformation> cs,
            final Collection<PushdownReturnInformation> rs) {
        super("SMTPushdownAutomaton", "SMTPushdownAutomaton");
        this.init = i;
        this.procedures = ImmutableCreator.create(ps);
        this.calls = ImmutableCreator.create(cs);
        this.returns = ImmutableCreator.create(rs);
    }

    @Override
    public String getStrategyName() {
        throw new NotYetImplementedException(); //We can't process these (yet)
    }

    /** {@inheritDoc} */
    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        this.toSMTOutput(res);
        return (o.verb(res.toString()));
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        this.toSMTOutput(res);
        return (res.toString());
    }

    public void toSMTOutput(StringBuilder s) {
        final Set<String> allLocations = new LinkedHashSet<>();
        for (PushdownProcedureInformation proc : this.procedures) {
            allLocations.addAll(proc.getUsedLocations());
        }

        s.append("(declare-sort Loc 0)\n");
        for (String loc : allLocations) {
            s.append("(declare-const ")
             .append(loc)
             .append(" Loc)\n");
        }
        s.append("(assert (distinct ");
        for (String loc : allLocations) {
            s.append(loc).append(" ");
        }
        s.append("))\n\n");

        s.append("(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool\n");
        s.append("  (and (= pc src) rel))\n\n");

        s.append("(define-fun cfg_trans2 ( (pc Loc) (src Loc)\n");
        s.append("                         (pc1 Loc) (dst Loc)\n");
        s.append("                         (rel Bool) ) Bool\n");
        s.append("  (and (= pc src) (= pc1 dst) rel))\n\n");

        s.append("(define-fun cfg_trans3 ( (pc Loc) (exit Loc)\n");
        s.append("                         (pc1 Loc) (call Loc)\n");
        s.append("                         (pc2 Loc) (return Loc)\n");
        s.append("                         (rel Bool) ) Bool\n");
        s.append("  (and (= pc exit) (= pc1 call) (= pc2 return) rel))\n\n");

        this.init.toSMTOutput(s);
        for (PushdownProcedureInformation proc : this.procedures) {
            proc.toSMTOutput(s);
        }
        for (PushdownCallInformation proc : this.calls) {
            proc.toSMTOutput(s);
        }
        for (PushdownReturnInformation proc : this.returns) {
            proc.toSMTOutput(s);
        }
    }
}

