package aprove.verification.complexity.Utility;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class SparenessApproximation {

	private RuleSet trs;
	private TRSFunctionApplication hole;
	private RenamingCentral renamingCentral;
	private Set<Context> duplicatingContexts;
	private DefinedContextComputation dcc;

	public SparenessApproximation(RuleSet trs) {
		this.trs = trs;
		Set<String> lockedNames = trs.getUsedNames();
		renamingCentral = new RenamingCentral(lockedNames);
		hole = TRSTerm.createFunctionApplication(renamingCentral.freshConstant("[]"));
	}

	public Optional<DefaultProof> run(boolean weakly) {
	    if (weakly) {
	        duplicatingContexts = weaklyDuplicatingContexts();
	    } else {
	        duplicatingContexts = duplicatingContexts();
	    }
		if (duplicatingContexts.isEmpty()) {
            return Optional.of(new SparenessProof(weakly));
        }
		dcc = new DefinedContextComputation(trs, renamingCentral);
		for (Entry<Context, Boolean> e: dcc.definedContexts().entrySet()) {
			Context defContext = e.getKey();
			boolean info = e.getValue();
			Position defPos = defContext.getPosition();
			for (Context dupContext: duplicatingContexts) {
				Position dupPos = dupContext.getPosition();
				Position prefix;
				if (defPos.isPrefixOf(dupPos)) {
					prefix = defPos;
					if (!defPos.equals(dupPos) && info) {
						continue;
					}
				} else if (dupPos.isPrefixOf(defPos)) {
					prefix = dupPos;
				} else {
					continue;
				}
				TRSTerm defTerm = toTerm(defContext).replaceAt(prefix, hole);
				TRSTerm dupTerm = toTerm(dupContext).replaceAt(prefix, hole).renameVariables(defTerm.getVariables());
				if (dupTerm.unifies(defTerm)) {
					return Optional.empty();
				}
			}
		}
		return Optional.of(new SparenessProof(weakly));
	}


	/**
	 * Computes for each duplicating rule the context surrounding the duplicated variable on the lhs.
	 */
	Set<Context> duplicatingContexts() {
		Set<Context> res = new LinkedHashSet<>();
		for (Rule r: trs.getRules()) {
			TRSFunctionApplication lhs = r.getLeft();
			TRSTerm rhs = r.getRight();
			Map<TRSVariable, List<Position>> lhsVarPositions = lhs.getVariablePositions();
			Map<TRSVariable, List<Position>> rhsVarPositions = rhs.getVariablePositions();
			for (Entry<TRSVariable, List<Position>> e: rhsVarPositions.entrySet()) {
				TRSVariable x = e.getKey();
				List<Position> rhsPositions = e.getValue();
				if (rhsPositions.size() >= 2) {
					for (Position pi: lhsVarPositions.get(x)) {
						res.add(Context.create(lhs, pi));
					}
				}
			}
		}
		return res;
	}

    /**
     * Computes for each duplicating rule the context surrounding the weakly duplicated variable on the lhs.
     */
    Set<Context> weaklyDuplicatingContexts() {
        Set<Context> res = new LinkedHashSet<>();
        for (Rule r: trs.getRules()) {
            TRSFunctionApplication lhs = r.getLeft();
            TRSTerm rhs = r.getRight();
            Map<TRSVariable, List<Position>> lhsVarPositions = lhs.getVariablePositions();
            Map<TRSVariable, List<Position>> rhsVarPositions = rhs.getVariablePositions();
            for (Entry<TRSVariable, List<Position>> e: rhsVarPositions.entrySet()) {
                TRSVariable x = e.getKey();
                List<Position> rhsPositions = e.getValue();
                if (rhsPositions.size() > lhsVarPositions.get(x).size()) {
                    for (Position pi: lhsVarPositions.get(x)) {
                        res.add(Context.create(lhs, pi));
                    }
                }
            }
        }
        return res;
    }

	TRSTerm toTerm(Context c) {
		return c.replace(hole);
	}

	private class SparenessProof extends DefaultProof {
	    
	    final boolean weakly;
	    
	    public SparenessProof(boolean weakly) {
	        this.weakly = weakly;
	    }

		@Override
		public String export(Export_Util o, VerbosityLevel level) {
			StringBuilder proof = new StringBuilder();
			if (duplicatingContexts.isEmpty()) {
                proof.append(o.export("As the TRS is a non-duplicating, it is spare."));
            } else if (dcc.definedContexts().isEmpty()) {
				proof.append(o.export("As the TRS does not nest defined symbols, it is spare."));
			} else {
				proof.append(o.export("The"));
				if (weakly) {
	                proof.append(o.export(" (weakly)"));
				}
				proof.append(o.export(" duplicating contexts are:"));
				proof.append(o.linebreak());
				for (Context c: duplicatingContexts) {
					proof.append(o.export(c.getAsTerm().export(o)));
					proof.append(o.linebreak());
				}
				proof.append(o.paragraph());
				proof.append(o.export("The defined contexts are:"));
				proof.append(o.linebreak());
				proof.append(dcc.export(o));
				proof.append(o.export("As the defined contexts and the duplicating contexts do not overlap, the system is spare."));
			}
			return proof.toString();
		}

	}

}
