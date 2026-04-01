package aprove.verification.complexity.CpxTrsProblem.Processors.Utility;

import static aprove.verification.complexity.Utility.Util.*;
import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class DependencyGraphComputation {

        private RuntimeComplexityTrsProblem trs;
        private Set<Rule> reachableRules;
        private boolean done = false;
        private RenamingCentral renamingCentral;

        private class DependencyGraphProof extends DefaultProof {

            @Override
            public String export(Export_Util o, VerbosityLevel level) {
                Set<Rule> removedRules = new LinkedHashSet<>(trs.getRules());
                removedRules.removeAll(reachableRules);
                StringBuilder proof = new StringBuilder();
                proof.append(o.escape("The following rules are not reachable from basic terms in the dependency graph and can be removed:"));
                proof.append(o.newline());
                for (Rule r: removedRules) {
                    proof.append(r.export(o));
                    proof.append(o.linebreak());
                }
                return proof.toString();
            }

        }

        public DependencyGraphComputation(CpxRelTrsProblem trs) {
            this(trs.getRules());
        }

        public DependencyGraphComputation(Set<Rule> rules) {
            this.trs = RuntimeComplexityTrsProblem.create(ImmutableCreator.create(rules), RewriteStrategy.FULL);
            this.reachableRules = rules.stream().filter(x -> trs.isBasic(x.getLeft())).collect(toSet());
            this.renamingCentral = new RenamingCentral(trs.getUsedNames());
        }

        public Set<Rule> reachableRules() {
            if (!done) {
                while(updateReachableRules());
                done = true;
            }
            return reachableRules;
        }

        private boolean updateReachableRules() {
            Set<Rule> toAdd = new LinkedHashSet<>();
            for (Rule r: trs.getRules()) {
                for (Rule ar: reachableRules) {
                    for (TRSFunctionApplication rhsSub: ar.getRight().getNonVariableSubTerms()) {
                        if (trs.isDefined(rhsSub.getRootSymbol())) {
                            TRSTerm abstracted = linearizeAndAbstractInnerOccurrencesOf(rhsSub, trs.getDefinedSymbols(), renamingCentral);
                            if (abstracted.renameVariables(r.getLeft().getVariables()).unifies(r.getLeft())) {
                                toAdd.add(r);
                            }
                        }
                    }
                }
            }
            return reachableRules.addAll(toAdd);
        }

        public Proof getProof() {
            return new DependencyGraphProof();
        }

}
