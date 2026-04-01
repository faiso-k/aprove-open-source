package aprove.verification.complexity.LowerBounds;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class LemmaGenerator {

    private ConjectureGenerator recursionDepthConjectureGenerator;
    private ConjectureGenerator identityConjectureGenerator;
    private ConjectureGenerator indefiniteConjectureGenerator;
    private LowerBoundsToolbox toolbox;
    private TermRewriter rewriter;
    private NarrowingTree tree;
    private Abortion abortion;

    private Conjecture indefiniteConjecture = null;
    private Set<InductionProof> indefiniteProofs = Collections.emptySet();

    private Conjecture recursionDepthConjecture = null;
    private Set<InductionProof> recursionDepthProofs = Collections.emptySet();

    private Conjecture identityConjecture = null;
    private Set<InductionProof> identityProofs = Collections.emptySet();

    public LemmaGenerator(LowerBoundsToolbox toolbox, Abortion abortion) {
        this.toolbox = toolbox;
        this.rewriter = new TermRewriter(toolbox);
        this.abortion = abortion;
        TRSFunctionApplication startTerm = toolbox.termGenerator.generate(toolbox.toAnalyze);
        this.tree = new NarrowingTree(toolbox, startTerm, abortion);
        this.recursionDepthConjectureGenerator = new ConjectureGenerator(new GenerateDefiniteConjectureViaRecursionDepth(toolbox), this.tree);
        this.identityConjectureGenerator = new ConjectureGenerator(new GenerateDefiniteConjectureViaIdentity(toolbox), this.tree);
        this.indefiniteConjectureGenerator = new ConjectureGenerator(new IndefiniteConjectureGenerationHeuristic(toolbox), this.tree);
    }

    void generate(boolean indefinite) {
        for (int i = 1; i <= 10; i++) {
            this.abortion.checkAbortion();
            boolean finished = this.tree.enlarge(i*5);
            this.recursionDepthConjecture = this.recursionDepthConjectureGenerator.generate();
            if (this.recursionDepthConjecture != null) {
                this.recursionDepthProofs = this.recursionDepthConjecture.getProver(this.toolbox, this.rewriter).prove();
                if (!this.recursionDepthProofs.isEmpty()) {
                    return;
                }
                if (indefinite && this.indefiniteProofs.isEmpty()) {
                    this.indefiniteConjecture = this.recursionDepthConjecture.toIndefiniteConjecture(this.toolbox);
                    this.indefiniteProofs = this.indefiniteConjecture.getProver(this.toolbox, this.rewriter).prove();
                }
            }
            if (finished) {
                break;
            }
        }
        this.identityConjecture = this.identityConjectureGenerator.generate();
        if (this.identityConjecture != null) {
            this.identityProofs = this.identityConjecture.getProver(this.toolbox, this.rewriter).prove();
            if (!this.identityProofs.isEmpty()) {
                return;
            } else if (indefinite && this.indefiniteProofs.isEmpty()) {
                this.indefiniteConjecture = this.identityConjecture.toIndefiniteConjecture(this.toolbox);
                this.indefiniteProofs = this.indefiniteConjecture.getProver(this.toolbox, this.rewriter).prove();
            }
        }
        if (indefinite && this.indefiniteProofs.isEmpty()) {
            this.indefiniteConjecture = this.indefiniteConjectureGenerator.generate();
            if (this.indefiniteConjecture != null) {
                this.indefiniteProofs = this.indefiniteConjecture.getProver(this.toolbox, this.rewriter).prove();
            }
        }
    }

    public Pair<Conjecture, Set<InductionProof>> result() {
        if (!this.recursionDepthProofs.isEmpty()) {
            return new Pair<>(this.recursionDepthConjecture, this.recursionDepthProofs);
        } else if (!this.identityProofs.isEmpty()) {
            return new Pair<>(this.identityConjecture, this.identityProofs);
        } else if (!this.indefiniteProofs.isEmpty()) {
            return new Pair<>(this.indefiniteConjecture, this.indefiniteProofs);
        } else {
            return null;
        }
    }
}
