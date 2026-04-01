/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class IdpCritPairsIterator implements AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> {
    private static final int MASK = 0x20;

    private final GeneralizedRule[] rootRules;
    private int posRoot;
    private int posOther;
    private final int n;
    private final int n_minus_1;
    private boolean nextValid;
    private ImmutableTriple<TRSTerm, TRSTerm, Boolean> nextCritPair;
    private Iterator<Pair<Position, TRSFunctionApplication>> currentOtherPositions;
    private int count = 0;

    /**
     * a critPairIterator takes a set of rules and iterates over
     * all critical pairs. Non-root overlaps will be returned before
     * root overlaps.
     * @param rules
     */
    public IdpCritPairsIterator(Set<GeneralizedRule> rules) {
        this.n = rules.size();
        this.n_minus_1 = this.n - 1;
        this.rootRules = new GeneralizedRule[this.n];
        int i = 0;

        for (GeneralizedRule rule : rules) {
            this.rootRules[i] = rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
            i++;
        }

        if (this.n == 0) {
            this.nextValid = true;
        } else {
            this.nextValid = false;
            this.currentOtherPositions = this.rootRules[0].getLeft().getNonRootNonVariablePositionsWithSubTerms().iterator();
        }
        this.posRoot = 0;
        this.posOther = 0;
        this.nextCritPair = null;
    }

    private void computeNext(Abortion aborter) throws AbortionException {
        if (this.currentOtherPositions != null) {
            while (this.posRoot != this.n) {
                GeneralizedRule rootRule = this.rootRules[this.posRoot];
                TRSTerm left = rootRule.getLhsInStandardRepresentation();
                TRSTerm right = rootRule.getRhsInStandardRepresentation();
                while (this.posOther != this.n) {
                    GeneralizedRule otherRule = this.rootRules[this.posOther];
                    TRSTerm otherLeft = otherRule.getLeft();
                    TRSTerm otherRight = otherRule.getRight();
                    if (this.currentOtherPositions == null) {
                        this.currentOtherPositions = otherLeft.getNonRootNonVariablePositionsWithSubTerms().iterator();
                    }
                    while (this.currentOtherPositions.hasNext()) {
                        this.count++;
                        if ((this.count & IdpCritPairsIterator.MASK) != 0) {
                            this.count = 0;
                            aborter.checkAbortion();
                        }
                        Pair<Position, TRSFunctionApplication> posAndSubLeft = this.currentOtherPositions.next();
                        TRSFunctionApplication subLeft = posAndSubLeft.y;
                        TRSSubstitution sigma = left.getMGU(subLeft);
                        if (sigma != null) {
                            TRSTerm otherRightSigma = otherRight.applySubstitution(sigma);
                            TRSTerm otherLeftRightAtP_sigma = otherLeft.replaceAt(posAndSubLeft.x, right).applySubstitution(sigma);
                            this.nextCritPair = new ImmutableTriple<TRSTerm, TRSTerm, Boolean>(otherRightSigma, otherLeftRightAtP_sigma, false);
                            this.nextValid = true;
                            return;
                        }
                    }
                    this.posOther++;
                    this.currentOtherPositions = null;
                }
                this.posRoot ++;
                this.posOther = 0;
            }
            this.posRoot = 0;
            this.posOther = 1;
        }


        while (this.posRoot != this.n_minus_1) {
            GeneralizedRule rootRule = this.rootRules[this.posRoot];
            TRSTerm left = rootRule.getLhsInStandardRepresentation();
            TRSTerm right = rootRule.getRhsInStandardRepresentation();
            while (this.posOther != this.n) {
                GeneralizedRule otherRule = this.rootRules[this.posOther];
                TRSTerm otherLeft = otherRule.getLeft();
                this.posOther++;
                TRSSubstitution sigma = left.getMGU(otherLeft);
                if (sigma != null) {
                    TRSTerm rightSigma = right.applySubstitution(sigma);
                    TRSTerm otherRightSigma = otherRule.getRight().applySubstitution(sigma);
                    this.nextCritPair = new ImmutableTriple<TRSTerm, TRSTerm, Boolean>(rightSigma, otherRightSigma, true);
                    this.nextValid = true;
                    return;
                }
            }
            this.posRoot++;
            this.posOther = this.posRoot+1;
        }

        this.nextCritPair = null;
        this.nextValid = true;
    }

    @Override
    public boolean hasNext(Abortion aborter) throws AbortionException {
        if (!this.nextValid) {
            this.computeNext(aborter);
        }
        return this.nextCritPair != null;
    }

    @Override
    public ImmutableTriple<TRSTerm, TRSTerm, Boolean> next(Abortion aborter) throws AbortionException {
        if (this.hasNext(aborter)) {
            this.nextValid = false;
            return this.nextCritPair;
        } else {
            throw new NoSuchElementException();
        }
    }

}
