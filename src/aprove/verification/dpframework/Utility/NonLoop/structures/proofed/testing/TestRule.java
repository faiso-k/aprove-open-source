package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.testing;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class TestRule extends ProofedRule {

    private TestRule(final PatternTerm lhs, final PatternTerm rhs, final ImmutableSet<Rule> R,
            final ImmutableSet<Rule> P, final boolean hasPStep) {
        super(lhs, rhs, R, P, hasPStep);
    }

    public static ProofedRule create(final PatternTerm lhs,
        final PatternTerm rhs,
        final ImmutableSet<Rule> R,
        final ImmutableSet<Rule> P,
        final boolean hasPStep) {

        return new TestRule(lhs, rhs, R, P, hasPStep);
    }
    
    @Override
    public int getProofStepCount() {
        return 0;
    }
    
    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        return ImmutableCreator.create(new ArrayList<Pair<Position, Rule>>());
    }

    @Override
    public String toString() {
        return super.toString() + " TestRule";
    }

    @Override
    public String exportProof(final Export_Util eu) {
        return "TestRule";
    }

    @Override
    public String exportProofShort(final Export_Util eu) {
        return "TestRule";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportParents(final Export_Util eu,
        final String indent,
        final String addIndent,
        final boolean firstIntermediate,
        final boolean fullProof) {
        return "";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException("TestRule not certifiable.");
    }

}
