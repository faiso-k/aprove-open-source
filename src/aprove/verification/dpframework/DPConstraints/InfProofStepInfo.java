package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.InductionCalculusProof.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

public interface InfProofStepInfo {

    Element toDOM(Document doc, XMLMetaData xmlMetaData, List<Element> prfs, Kind kind, TRSTerm fc);

    Element toCPF(Document doc, XMLMetaData xmlMetaData, List<Element> prfs, Kind kind, TRSTerm fc);

    List<Implication> result();

    public static InfProofStepInfo INF_DUMMY_PROOF = new InfProofStepInfo() {

        @Override
        public Element toCPF(
            final Document doc,
            final XMLMetaData xmlMetaData,
            final List<Element> prfs,
            final Kind kind,
            final TRSTerm fc)
        {
            return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(doc, CPFTag.FINAL.create(doc));
        }


        @Override
        public List<Implication> result() {
            return new ArrayList<>(0);
        }

        @Override
        public Element toDOM(
            final Document doc,
            final XMLMetaData xmlMetaData,
            final List<Element> prfs,
            final Kind kind,
            final TRSTerm fc)
        {
            return this.toCPF(doc, xmlMetaData, prfs, kind, fc);
        }

    };

}

class InfProofStepConstants {
    final static String CCP = "conditionalConstraintProof";
}

abstract class InfProofStepSingleInfo implements InfProofStepInfo {

    public abstract Element toDOM(Document doc, XMLMetaData xmlMetaData, Element prf, Kind kind, TRSTerm fc);

    public abstract Element toCPF(Document doc, XMLMetaData xmlMetaData, Element prf, Kind kind, TRSTerm fc);

    final Implication newImp;

    public InfProofStepSingleInfo(final Implication newImp) {
        this.newImp = newImp;
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final List<Element> prfs,
        final Kind kind,
        final TRSTerm fc)
    {
        return this.toDOM(doc, xmlMetaData, prfs.get(0), kind, fc);
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final List<Element> prfs,
        final Kind kind,
        final TRSTerm fc)
    {
        return this.toCPF(doc, xmlMetaData, prfs.get(0), kind, fc);
    }

    @Override
    public List<Implication> result() {
        final List<Implication> res = new ArrayList<>(1);
        res.add(this.newImp);
        return res;
    }
}

class InfRule1DifferentConstructorProof implements InfProofStepInfo {

    final Constraint reduce;

    public InfRule1DifferentConstructorProof(final Constraint reduce) {
        this.reduce = reduce;
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final List<Element> prfs,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element e = doc.createElement(InfProofStepConstants.CCP);
        final Element ee = doc.createElement("differentConstructor");
        final Element c = InductionCalculusProof.toDOM(doc, this.reduce, kind, fc, xmlMetaData);
        ee.appendChild(c);
        e.appendChild(ee);
        return e;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final List<Element> prfs,
        final Kind kind,
        final TRSTerm fc)
    {
        return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(
            doc,
            CPFTag.DIFFERENT_CONSTRUCTOR.create(
                doc,
                InductionCalculusProof.toCPF(doc, this.reduce, kind, fc, xmlMetaData)));
    }

    @Override
    public List<Implication> result() {
        return new ArrayList<>(0);
    }

}

class InfRule4DeleteProof extends InfProofStepSingleInfo {

    public InfRule4DeleteProof(final Implication imp) {
        super(imp);
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element e = doc.createElement(InfProofStepConstants.CCP);
        final Element ee = doc.createElement("deleteCondition");
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.newImp, kind, fc, xmlMetaData));
        ee.appendChild(prf);
        e.appendChild(ee);
        return e;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(
            doc,
            CPFTag.DELETE_CONDITION.create(doc,
                InductionCalculusProof.toCPF(doc, this.newImp, kind, fc, xmlMetaData),
                prf));
    }

}

class InfRule2SameConstructorProof extends InfProofStepSingleInfo {

    final Constraint reduce;

    public InfRule2SameConstructorProof(final Constraint reduce, final Implication newImp) {
        super(newImp);
        this.reduce = reduce;
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element e = doc.createElement(InfProofStepConstants.CCP);
        final Element ee = doc.createElement("sameConstructor");
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.reduce, kind, fc, xmlMetaData));
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.newImp, kind, fc, xmlMetaData));
        ee.appendChild(prf);
        e.appendChild(ee);
        return e;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(
            doc,
            CPFTag.SAME_CONSTRUCTOR.create(doc,
                InductionCalculusProof.toCPF(doc, this.reduce, kind, fc, xmlMetaData),
                InductionCalculusProof.toCPF(doc, this.newImp, kind, fc, xmlMetaData),
                prf));
    }

}

class InfRule3VariableEquationProof extends InfProofStepSingleInfo {

    final TRSVariable x;
    final TRSTerm t;

    public InfRule3VariableEquationProof(final TRSVariable x, final TRSTerm t, final Implication newImp) {
        super(newImp);
        this.x = x;
        this.t = t;
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element e = doc.createElement(InfProofStepConstants.CCP);
        final Element ee = doc.createElement("variableEquation");
        ee.appendChild(this.x.toDOM(doc, xmlMetaData));
        ee.appendChild(this.t.toDOM(doc, xmlMetaData));
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.newImp, kind, fc, xmlMetaData));
        ee.appendChild(prf);
        e.appendChild(ee);
        return e;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(doc, CPFTag.VARIABLE_EQUATION.create(
            doc,
            this.x.toCPF(doc, xmlMetaData),
            this.t.toCPF(doc, xmlMetaData),
            InductionCalculusProof.toCPF(doc, this.newImp, kind, fc, xmlMetaData),
            prf));
    }

}

class InfRule5InductionProof implements InfProofStepInfo {

    final Constraint reducesTo;
    final ConstraintSet phi;
    final Map<GeneralizedRule, Triple<Implication, List<Pair<TRSTerm, List<TRSVariable>>>, Constraint>> ihs;

    public InfRule5InductionProof(final Constraint reducesTo, final ConstraintSet phi) {
        this.reducesTo = reducesTo;
        this.phi = phi;
        this.ihs = new LinkedHashMap<>();
    }

    public void addIH(
        final GeneralizedRule rule,
        final Implication imp,
        final List<Pair<TRSTerm, List<TRSVariable>>> subtermEntries,
        final Constraint ruleIreduce)
    {
        final Triple<Implication, List<Pair<TRSTerm, List<TRSVariable>>>, Constraint> triple =
            new Triple<>(imp, subtermEntries, ruleIreduce);
        this.ihs.put(rule, triple);
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final List<Element> prfs,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element e = doc.createElement(InfProofStepConstants.CCP);
        final Element ee = doc.createElement("induction");
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.reducesTo, kind, fc, xmlMetaData));
        final Element conjs = doc.createElement("conjuncts");
        for (final Constraint c : this.phi) {
            conjs.appendChild(InductionCalculusProof.toDOM(doc, c, kind, fc, xmlMetaData));
        }
        ee.appendChild(conjs);
        final Element recs = doc.createElement("ruleConstraintProofs");
        int i = 0;
        for (final Map.Entry<GeneralizedRule, Triple<Implication, List<Pair<TRSTerm, List<TRSVariable>>>, Constraint>> entry : this.ihs
            .entrySet())
        {
            final Element ih = doc.createElement("ruleConstraintProof");
            ih.appendChild(entry.getKey().toDOM(doc, xmlMetaData));
            final Implication imp = entry.getValue().x;
            final List<Pair<TRSTerm, List<TRSVariable>>> substEntries = entry.getValue().y;
            final Constraint reduce = entry.getValue().z;
            final Element ses = doc.createElement("subtermVarEntries");
            if (substEntries != null) {
                for (final Pair<TRSTerm, List<TRSVariable>> pair : substEntries) {
                    final Element se = doc.createElement("subtermVarEntry");
                    se.appendChild(pair.x.toDOM(doc, xmlMetaData));
                    for (final TRSVariable x : pair.y) {
                        se.appendChild(x.toDOM(doc, xmlMetaData));
                    }
                    ses.appendChild(se);
                }
            }
            ih.appendChild(ses);
            ih.appendChild(InductionCalculusProof.toDOM(doc, imp, kind, fc, xmlMetaData));
            if (reduce == null) {
                ih.appendChild(prfs.get(i));
                i++;
            } else {
                ih.appendChild((new InfRule1DifferentConstructorProof(reduce)).toDOM(
                    doc,
                    xmlMetaData,
                    new ArrayList<Element>(0),
                    kind,
                    fc));
            }
            recs.appendChild(ih);
        }
        ee.appendChild(recs);
        e.appendChild(ee);
        return e;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final List<Element> prfs,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element conjs = CPFTag.CONJUNCTS.create(doc);
        for (final Constraint c : this.phi) {
            conjs.appendChild(InductionCalculusProof.toCPF(doc, c, kind, fc, xmlMetaData));
        }
        final Element recs = CPFTag.RULE_CONSTRAINT_PROOFS.create(doc);
        int i = 0;
        for (final Map.Entry<GeneralizedRule, Triple<Implication, List<Pair<TRSTerm, List<TRSVariable>>>, Constraint>> entry : this.ihs
            .entrySet())
        {
            final Implication imp = entry.getValue().x;
            final List<Pair<TRSTerm, List<TRSVariable>>> substEntries = entry.getValue().y;
            final Constraint reduce = entry.getValue().z;
            final Element ses = CPFTag.SUBTERM_VAR_ENTRIES.create(doc);
            if (substEntries != null) {
                for (final Pair<TRSTerm, List<TRSVariable>> pair : substEntries) {
                    final Element se = CPFTag.SUBTERM_VAR_ENTRY.create(doc);
                    se.appendChild(pair.x.toCPF(doc, xmlMetaData));
                    for (final TRSVariable x : pair.y) {
                        se.appendChild(x.toCPF(doc, xmlMetaData));
                    }
                    ses.appendChild(se);
                }
            }
            final Element ih = CPFTag.RULE_CONSTRAINT_PROOF.create(doc,
                entry.getKey().toCPF(doc, xmlMetaData),
                ses,
                InductionCalculusProof.toCPF(doc, imp, kind, fc, xmlMetaData));
            if (reduce == null) {
                ih.appendChild(prfs.get(i));
                i++;
            } else {
                ih.appendChild((new InfRule1DifferentConstructorProof(reduce)).toCPF(
                    doc,
                    xmlMetaData,
                    new ArrayList<Element>(0),
                    kind,
                    fc));
            }
            recs.appendChild(ih);
        }
        final Element ee = CPFTag.INDUCTION.create(doc,
            InductionCalculusProof.toCPF(doc, this.reducesTo, kind, fc, xmlMetaData),
            conjs,
            recs);
        return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(doc, ee);
    }

    @Override
    public List<Implication> result() {
        final List<Implication> arr = new ArrayList<>();
        for (final Map.Entry<GeneralizedRule, Triple<Implication, List<Pair<TRSTerm, List<TRSVariable>>>, Constraint>> entry : this.ihs
            .entrySet())
        {
            if (entry.getValue().z == null) {
                arr.add(entry.getValue().x);
            }
        }
        return arr;
    }

}

class InfRule6SimplifyProof extends InfProofStepSingleInfo {

    final Implication ih;
    final TRSSubstitution sigma;

    public InfRule6SimplifyProof(final Implication ih, final TRSSubstitution sigma, final Implication newImp) {
        super(newImp);
        this.ih = ih;
        this.sigma = sigma;
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        final Element e = doc.createElement(InfProofStepConstants.CCP);
        final Element ee = doc.createElement("simplifyCondition");
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.ih, kind, fc, xmlMetaData));
        ee.appendChild(this.sigma.toDOM(doc, xmlMetaData));
        ee.appendChild(InductionCalculusProof.toDOM(doc, this.newImp, kind, fc, xmlMetaData));
        ee.appendChild(prf);
        e.appendChild(ee);
        return e;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        return CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(doc,
            CPFTag.SIMPLIFY_CONDITION.create(doc,
                InductionCalculusProof.toCPF(doc, this.ih, kind, fc, xmlMetaData),
                this.sigma.toCPF(doc, xmlMetaData),
                InductionCalculusProof.toCPF(doc, this.newImp, kind, fc, xmlMetaData),
                prf));
    }


}

class InfRule7DefinedVarProof extends InfProofStepSingleInfo {

    final Implication oldImp;
    final ReducesTo reduce;
    final Map<Integer, TRSVariable> newVars;

    public InfRule7DefinedVarProof(
        final Implication oldImp,
        final ReducesTo reduce,
        final Map<Integer, TRSVariable> newVars,
        final Implication newImp)
    {
        super(newImp);
        this.oldImp = oldImp;
        this.reduce = reduce;
        this.newVars = newVars;
    }

    @Override
    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        final Map<Integer, TRSVariable> newVars = new LinkedHashMap<>(this.newVars);
        final Constraint conc = this.oldImp.conclusion;
        final ConstraintSet pprems = this.oldImp.getConditions();
        assert (this.oldImp.quantor.isEmpty());
        final Set<Constraint> prems = new LinkedHashSet<>(pprems);
        final boolean removed = prems.remove(this.reduce);
        assert (removed);
        final Set<TRSVariable> empty = new HashSet<>(0);
        final TRSFunctionApplication fts = (TRSFunctionApplication) this.reduce.getLeft();
        final FunctionSymbol f = fts.getRootSymbol();
        final int n = f.getArity();
        final TRSTerm r = this.reduce.getRight();
        Implication newImp = this.newImp;
        Element currentPrf = prf;
        final Iterator<Map.Entry<Integer, TRSVariable>> iter = newVars.entrySet().iterator();
        while (iter.hasNext()) {
            final Map.Entry<Integer, TRSVariable> iv = iter.next();
            iter.remove();
            final Element e = doc.createElement(InfProofStepConstants.CCP);
            final Element ee = doc.createElement("funargIntoVar");
            final ArrayList<TRSTerm> args = new ArrayList<>(n);
            for (int j = 0; j < n; j++) {
                TRSTerm t = newVars.get(Integer.valueOf(j));
                if (t == null) {
                    t = fts.getArgument(j);
                }
                args.add(t);
            }
            final TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(f, args);
            final ReducesTo reduce = ReducesTo.create(lhs, r, null, null, null);
            ee.appendChild(InductionCalculusProof.toDOM(doc, reduce, kind, fc, xmlMetaData));
            final Element p = XMLTag.POSITION.createElement(doc);
            p.setTextContent("" + (iv.getKey() + 1));
            ee.appendChild(p);
            ee.appendChild(iv.getValue().toDOM(doc, xmlMetaData));
            ee.appendChild(InductionCalculusProof.toDOM(doc, newImp, kind, fc, xmlMetaData));
            final Set<Constraint> newPrems = new LinkedHashSet<>(prems);
            for (final Map.Entry<Integer, TRSVariable> jx : newVars.entrySet()) {
                newPrems.add(ReducesTo.create(fts.getArgument(jx.getKey()), jx.getValue(), null, null, null));
            }
            newPrems.add(reduce);
            newImp = Implication.create(empty, ConstraintSet.create(newPrems), conc, null);
            ee.appendChild(currentPrf);
            e.appendChild(ee);
            currentPrf = e;
        }
        return currentPrf;
    }

    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Element prf,
        final Kind kind,
        final TRSTerm fc)
    {
        final Map<Integer, TRSVariable> newVars = new LinkedHashMap<>(this.newVars);
        final Constraint conc = this.oldImp.conclusion;
        final ConstraintSet pprems = this.oldImp.getConditions();
        assert (this.oldImp.quantor.isEmpty());
        final Set<Constraint> prems = new LinkedHashSet<>(pprems);
        final boolean removed = prems.remove(this.reduce);
        assert (removed);
        final Set<TRSVariable> empty = new HashSet<>(0);
        final TRSFunctionApplication fts = (TRSFunctionApplication) this.reduce.getLeft();
        final FunctionSymbol f = fts.getRootSymbol();
        final int n = f.getArity();
        final TRSTerm r = this.reduce.getRight();
        Implication newImp = this.newImp;
        Element currentPrf = prf;
        final Iterator<Map.Entry<Integer, TRSVariable>> iter = newVars.entrySet().iterator();
        while (iter.hasNext()) {
            final Map.Entry<Integer, TRSVariable> iv = iter.next();
            iter.remove();
            final Element e = CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(doc);
            final Element ee = CPFTag.FUNARG_INTO_VAR.create(doc);
            final ArrayList<TRSTerm> args = new ArrayList<>(n);
            for (int j = 0; j < n; j++) {
                TRSTerm t = newVars.get(Integer.valueOf(j));
                if (t == null) {
                    t = fts.getArgument(j);
                }
                args.add(t);
            }
            final TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(f, args);
            final ReducesTo reduce = ReducesTo.create(lhs, r, null, null, null);
            ee.appendChild(InductionCalculusProof.toCPF(doc, reduce, kind, fc, xmlMetaData));
            final Element p = CPFTag.POSITION.create(doc, doc.createTextNode("" + (iv.getKey() + 1)));
            ee.appendChild(p);
            ee.appendChild(iv.getValue().toCPF(doc, xmlMetaData));
            ee.appendChild(InductionCalculusProof.toCPF(doc, newImp, kind, fc, xmlMetaData));
            final Set<Constraint> newPrems = new LinkedHashSet<>(prems);
            for (final Map.Entry<Integer, TRSVariable> jx : newVars.entrySet()) {
                newPrems.add(ReducesTo.create(fts.getArgument(jx.getKey()), jx.getValue(), null, null, null));
            }
            newPrems.add(reduce);
            newImp = Implication.create(empty, ConstraintSet.create(newPrems), conc, null);
            ee.appendChild(currentPrf);
            e.appendChild(ee);
            currentPrf = e;
        }
        return currentPrf;
    }

}
