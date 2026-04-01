package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

@NoParams
public class IdentityTransformationSimplifier extends SimplifierProcessor {

    private SimplifierObligation obl;
    private Vector identityInfo;

    public IdentityTransformationSimplifier() {
        super("Identity Transformation Simplifier", "IT",
            "Identity Transformation");
    }

    @Override
    public SimplifierObligation simplify(final SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.identityInfo = new Vector();
        if (this.identityTransformation()) {
            this.setProof(new IdentityTransformationProof(oobl,
                this.identityInfo, this.obl));
            this.identityInfo = null;
            return this.obl;
        }
        this.identityInfo = null;
        return null;
    }

    /* Identity-Transformation */

    public boolean identityTransformation() {
        boolean changed = false;
        SimplifierProcessor.log.log(Level.FINER,
            "Simplifier: Performing identity-transformation.\n");
        final Iterator it = (new Vector(this.obl.defs)).iterator();
        while (it.hasNext()) {
            final DefFunctionSymbol def = (DefFunctionSymbol) it.next();
            final int sig = def.getSignatureClass();
            if (sig == Symbol.MAINSIG
                || (sig == Symbol.DEFAULTSIG && !this.obl.isProjection(def))) {
                final Object info = this.identityTransformation(def);
                changed = info != null || changed;
                if (info != null) {
                    this.identityInfo.add(info);
                }
            }
        }
        return changed;
    }

    public Object identityTransformation(final DefFunctionSymbol def) {
        Set<Rule> defrules = this.obl.defsrules.get(def);
        // There have to be at least two rules, otherwise this
        // transformation does not make any sense.
        if (defrules.size() < 2) {
            return null;
        }
        if (this.obl.ignoreIdentity.contains(def)) {
            return null;
        }
        final Vector<Rule> recrules = new Vector<Rule>();
        AlgebraTerm p = null;
        AlgebraTerm gleft = null;
        Iterator it = defrules.iterator();
        while (it.hasNext()) {
            final Rule r = this.obl.liftRule((Rule) it.next());
            final AlgebraTerm left = r.getLeft();
            final AlgebraTerm right = r.getRight();
            if (def.equals(right.getSymbol())) {
                recrules.add(r);
            } else {
                if (p == null) {
                    p = right;
                    gleft = left;
                } else {
                    try {
                        final AlgebraSubstitution sigma = left.matches(gleft);
                        if (!p.equals(right.apply(sigma))) {
                            return null;
                        }
                    } catch (final UnificationException e) {
                    }
                }
            }
        }
        it = recrules.iterator();
        while (it.hasNext()) {
            final Rule r = (Rule) it.next();
            final AlgebraTerm left = r.getLeft();
            AlgebraTerm right = r.getRight();
            try {
                final AlgebraSubstitution sigma = left.matches(gleft);
                right = right.apply(sigma);
            } catch (final UnificationException e) {
            }
            final AlgebraSubstitution sigma = AlgebraSubstitution.create();
            final Iterator x_it = gleft.getArguments().iterator();
            final Iterator r_it = right.getArguments().iterator();
            while (x_it.hasNext()) {
                final VariableSymbol xsym =
                    (VariableSymbol) (((AlgebraVariable) x_it.next()).getSymbol());
                sigma.put(xsym, (AlgebraTerm) r_it.next());
            }
            if (!p.equals(p.apply(sigma))) {
                return null;
            }
        }
        // Everything is fine. Do the transformation.
        final String name =
            this.obl.symbnames.getFreshName(def.getName(), false);
        final DefFunctionSymbol ndef =
            DefFunctionSymbol.create(name, def.getArgSorts(), def.getSort());

        final Type ndefType =
            this.obl.typeContext.getSingleTypeOf(def).deepcopy();
        this.obl.typeContext.setSingleTypeOf(ndef, ndefType);

        final Set<Rule> ndefrules = new HashSet<Rule>();
        it = defrules.iterator();
        while (it.hasNext()) {
            final Rule r = (Rule) it.next();
            final AlgebraTerm left =
                AlgebraFunctionApplication.create(ndef, r.getLeft().getArguments());
            final AlgebraTerm right =
                SimplifierObligation.replace_f_with_g(r.getRight(), def, ndef);
            ndefrules.add(Rule.create(r.getConds(), left, right));
        }
        this.obl.defs.add(ndef);
        this.obl.defsrules.put(ndef, ndefrules);
        this.obl.updateSymbol(ndef, ndefrules);
        defrules = new HashSet<Rule>();

        // the type of p is the result-type of def
        final AlgebraTerm pType =
            TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(def).getTypeMatrix());

        final List<AlgebraTerm> projargs = new Vector<AlgebraTerm>();
        final List<AlgebraTerm> projargsTypes = new Vector<AlgebraTerm>();
        projargs.add(AlgebraFunctionApplication.create(ndef, new Vector<AlgebraTerm>(
            gleft.getArguments())));
        projargsTypes.add(TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(
            ndef).getTypeMatrix()));

        final AlgebraTerm right =
            this.obl.makeProjectionTyped(p, pType, projargs, projargsTypes);

        final Rule nRule = Rule.create(gleft, right);
        defrules.add(nRule);
        this.obl.defsrules.put(def, defrules);
        this.obl.updateSymbol(def, defrules);
        this.obl.ignoreIdentity.add(ndef);
        return new Object[] { def, ndef, nRule };
    }

}
