package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class TypeInference extends AbstractIDPFilter<Result, IDPProblem> {

    public TypeInference() {
        super("TypeInference", FilterMode.QUANTIFY_FILTERED_VARIABLES);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem idp,
        final Abortion aborter) throws AbortionException {
        final Map<TypePos, Set<TypePos>> typePositions =
            new LinkedHashMap<TypePos, Set<TypePos>>();

        this.generateTermEqClasses(idp, typePositions, aborter);
        this.generateLoopRenamingEqClasses(idp, typePositions, aborter);
        this.generateNodeCondEqClasses(idp, typePositions, aborter);
        this.generateEdgeEqClasses(idp, typePositions, aborter);
        this.generateQEqClasses(idp, typePositions, aborter);

        try {
            final Map<Set<TypePos>, SemiRingDomain<?>> typeClasses =
                this.findEqClassDomains(idp, typePositions, aborter);

            final IDPProblem newIDP =
                this.createNewIDP(idp, typePositions, typeClasses, aborter);

            if (newIDP != idp) {
                return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT,
                    new TypeInferenceProof(typeClasses));
            }
        } catch (final BadTypeException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return ResultFactory.unsuccessful();
    }

    private void generateEdgeEqClasses(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();
        for (final Map.Entry<IEdge, Itpf> entry : graph.getEdgeConditions().entrySet()) {
            final IEdge edge = entry.getKey();
            this.typeItpf(entry.getValue(), edge, typePositions);
            final ITerm<?> from =
                graph.getTerm(edge.from).getSubterm(edge.fromPos);
            final ITerm<?> to = graph.getTerm(edge.to);

            final TypePos fromPos = TypePos.create(from);
            final TypePos toPos = TypePos.create(to);
            this.makeEquivalent(typePositions, fromPos, toPos);
        }
    }

    /**
     * @param idp
     * @param typePositions
     * @param aborter
     * @throws AbortionException
     */
    private void generateTermEqClasses(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Abortion aborter) throws AbortionException {
        for (final Map.Entry<INode, ? extends ITerm<?>> nodeTerm : idp.getIdpGraph().getNodeMap().entrySet()) {
            this.typeTerm(nodeTerm.getValue(),
                typePositions);
            aborter.checkAbortion();
        }
    }

    private void generateQEqClasses(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Abortion aborter) throws AbortionException {
        for (final ITerm<?> qTerm : idp.getIdpGraph().getQ().getUserDefinedTerms()) {
            this.typeTerm(qTerm, typePositions);
            aborter.checkAbortion();
        }
    }

    private void generateNodeCondEqClasses(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Abortion aborter) throws AbortionException {
        for (final Map.Entry<INode, Itpf> nodeCondition : idp.getIdpGraph().getNodeConditions().entrySet()) {
            this.typeItpf(nodeCondition.getValue(), nodeCondition.getKey(),
                typePositions);
            aborter.checkAbortion();
        }
    }

    private void generateLoopRenamingEqClasses(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Abortion aborter) {
        for (final Map.Entry<INode, VarRenaming> renaming : idp.getIdpGraph().getLoopRenamings().entrySet()) {
            for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> substEntry : renaming.getValue().getMap().entrySet()) {
                final TypePos keyTypePos =
                    new TypePos(substEntry.getKey());
                final TypePos valueTypePos =
                    new TypePos(substEntry.getValue());
                this.makeEquivalent(typePositions, keyTypePos, valueTypePos);
            }
        }
    }

    private void typeItpf(final Itpf itpf,
        final EdgeOrNode boundVarsReference,
        final Map<TypePos, Set<TypePos>> typePositions) {
        final Set<IVariable<?>> boundVariables = itpf.getBoundVariables();

        for (final ItpfConjClause clause : itpf.getClauses()) {
            for (final ItpfAtom atom : clause.getLiterals().keySet()) {
                if (atom.isItp()) {
                    final ItpfItp itp = (ItpfItp) atom;
                    this.typeTerm(itp.getL(), typePositions);
                    this.typeTerm(itp.getR(), typePositions);

                    switch (itp.getRelation()) {
                    case EQ:
                    case TO:
                    case TO_PLUS:
                    case TO_SYM_TRANS:
                    case TO_TRANS:
                        this.makeEquivalent(
                            typePositions,
                            TypePos.create(itp.getL()),
                            TypePos.create(itp.getR()));
                    default:
                    }
                } else if (atom.isPoly()) {
                    final Polynomial<?> poly = ((ItpfPolyAtom<?>) atom).getPoly();
                    this.typePoly(poly, boundVariables, boundVarsReference,
                        typePositions);
                } else {
                    throw new UnsupportedOperationException("unknown atom type: " + atom);
                }
            }
        }
    }

    private void typePoly(final Polynomial<?> poly,
        final Set<IVariable<?>> boundVariables,
        final EdgeOrNode reference,
        final Map<TypePos, Set<TypePos>> typePositions) {
        this.makeVarsEquivalent(typePositions, poly.getVariables());
    }

    private void typeTerm(final ITerm<?> t,
        final Map<TypePos, Set<TypePos>> typePositions) {
        if (!t.isVariable()) {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> root = fa.getRootSymbol();
            int i = 0;
            for (final ITerm<?> arg : fa.getArguments()) {
                final TypePos fInPos = new TypePos(root, i);
                TypePos argPos;
                if (arg.isVariable()) {
                    argPos = new TypePos((IVariable<?>) arg);
                } else {
                    final IFunctionApplication<?> argFa =
                        (IFunctionApplication<?>) arg;
                    argPos = new TypePos(argFa.getRootSymbol());
                    this.typeTerm(arg, typePositions);
                }
                this.makeEquivalent(typePositions, fInPos, argPos);
                i++;
            }
        }
    }

    private void makeEquivalent(final Map<TypePos, Set<TypePos>> typePositions,
        final Collection<TypePos> types) {
        if (types.size() <= 1) {
            return;
        }

        final Iterator<TypePos> typeIterator = types.iterator();

        final TypePos firstType = typeIterator.next();
        while(typeIterator.hasNext()) {
            this.makeEquivalent(typePositions, firstType, typeIterator.next());
        }
    }

    private void makeVarsEquivalent(final Map<TypePos, Set<TypePos>> typePositions,
        final Collection<? extends IVariable<?>> variables) {

        if (variables.size() <= 1) {
            return;
        }

        final Iterator<? extends IVariable<?>> varIterator = variables.iterator();

        final IVariable<?> firstVar = varIterator.next();
        final TypePos firstVarType = new TypePos(firstVar);
        while(varIterator.hasNext()) {
            final TypePos nextVarType = new TypePos(varIterator.next());
            this.makeEquivalent(typePositions, firstVarType, nextVarType);
        }
    }


    private void makeEquivalent(final Map<TypePos, Set<TypePos>> typePositions,
        final TypePos pos1,
        final TypePos pos2) {
        Set<TypePos> class1 = typePositions.get(pos1);
        final Set<TypePos> class2 = typePositions.get(pos2);
        if (class1 == null) {
            if (class2 == null) {
                class1 = new LinkedHashSet<TypePos>();
                class1.add(pos1);
                class1.add(pos2);
                typePositions.put(pos1, class1);
                typePositions.put(pos2, class1);
            } else {
                class2.add(pos1);
                typePositions.put(pos1, class2);
            }
        } else {
            if (class2 == null) {
                class1.add(pos2);
                typePositions.put(pos2, class1);
            } else {
                //merge
                for (final TypePos pos : class1) {
                    typePositions.put(pos, class2);
                }
                class2.addAll(class1);
            }
        }

    }

    private Map<Set<TypePos>, SemiRingDomain<?>> findEqClassDomains(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Abortion aborter) throws AbortionException, BadTypeException {
        final Map<Set<TypePos>, SemiRingDomain<?>> domainMap =
            new LinkedHashMap<Set<TypePos>, SemiRingDomain<?>>();

        int nextUserDefinedId = 0;

        for (final Set<TypePos> eqClass : typePositions.values()) {
            if (!domainMap.containsKey(eqClass)) {
                SemiRingDomain<?> dom = null;
                for (final TypePos pos : eqClass) {
                    if (pos.getFs() != null
                        && pos.getFs().getSemantics() != null) {
                        SemiRingDomain<?> addDom;
                        if (pos.isInput()) {
                            addDom = pos.getFs().getDomains().get(pos.getPos());
                        } else {
                            addDom = pos.getFs().getResultDomain();
                        }
                        if (dom == null) {
                            dom = addDom;
                        } else if (addDom.isSpecialization(dom)) {
                            dom = addDom;
                        } else {
                            throw new BadTypeException();
                        }
                    }
                }
                if (dom == null) {
                    dom = DomainFactory.createUserDefinedDomain(nextUserDefinedId, ImmutableCreator.create(Collections.<SemiRingDomain<?>>emptySet()));
                    nextUserDefinedId++;
                }
                domainMap.put(eqClass, dom);
            }
            aborter.checkAbortion();
        }

        return domainMap;
    }


    protected IDPProblem createNewIDP(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Map<Set<TypePos>, SemiRingDomain<?>> typeClasses,
        final Abortion aborter) throws AbortionException {

        final FunctionSymbolReplacement fsReplacement =
            this.createNewFunctionSymbols(idp, typePositions, typeClasses);

        final VarRenaming variableReplacement = this.createNewVariables(idp, typePositions, typeClasses);

        return this.createNewIDP(idp,
            new FilterReplacement(fsReplacement, variableReplacement),
            aborter);
    }

    protected FunctionSymbolReplacement createNewFunctionSymbols(final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Map<Set<TypePos>, SemiRingDomain<?>> typeClasses) {

        final IDPPredefinedMap predefinedMap = idp.getPredefinedMap();
        final FunctionSymbolReplacement fsReplacement =
            new FunctionSymbolReplacement();

        for (final IFunctionSymbol<?> fs : idp.getIdpGraph().getFunctionSymbols()) {
            if (fs.getSemantics() == null) {
                final List<SemiRingDomain<?>> inputDomains =
                    new ArrayList<SemiRingDomain<?>>(fs.getArity());
                for (int i = 0; i < fs.getArity(); i++) {
                    final SemiRingDomain<?> dom =
                        typeClasses.get(typePositions.get(new TypePos(fs, i)));
                    inputDomains.add(dom);
                }
                final SemiRingDomain<?> resultDomain =
                    typeClasses.get(typePositions.get(new TypePos(fs)));

                final IFunctionSymbol<?> newFs =
                    IFunctionSymbol.create(fs.getName(),
                        ImmutableCreator.create(inputDomains), resultDomain,
                        predefinedMap);

                final ArrayList<Boolean> retainedPositionsList = this.createRetainAllPositionsList(fs);

                fsReplacement.put(fs,
                    new ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>(newFs,
                            ImmutableCreator.create(retainedPositionsList)));
            }
        }
        return fsReplacement;
    }

    private ArrayList<Boolean> createRetainAllPositionsList(final IFunctionSymbol<?> fs) {
        final ArrayList<Boolean> res = new ArrayList<Boolean>(fs.getArity());

        for (int i = fs.getArity() - 1; i >= 0; i--) {
            res.add(Boolean.TRUE);
        }

        return res;
    }


    protected VarRenaming createNewVariables(
        final IDPProblem idp,
        final Map<TypePos, Set<TypePos>> typePositions,
        final Map<Set<TypePos>, SemiRingDomain<?>> typeClasses) {

        final Map<IVariable<?>, IVariable<?>> subst =
            new LinkedHashMap<IVariable<?>, IVariable<?>>();

        for (final Map.Entry<TypePos, Set<TypePos>> entry : typePositions.entrySet()) {
            if (entry.getKey().getVar() != null) {
                final IVariable<?> var = entry.getKey().getVar();
                final SemiRingDomain<?> newDom =
                    typeClasses.get(entry.getValue());
                final IVariable<?> newVar =
                    ITerm.createVariable(var.getName(),
                        newDom);
                subst.put(var, newVar);
            }
        }

        return VarRenaming.create(ImmutableCreator.create(subst),
            false,
            idp.getIdpGraph().getPolyFactory());
    }

    private static class TypePos implements Exportable {

        private final IFunctionSymbol<?> fs;
        private final Integer pos;
        private final boolean input;
        private final IVariable<?> var;
        private final int hash;

        public static TypePos create(final ITerm<?> t) {
            if (t.isVariable()) {
                return new TypePos((IVariable<?>) t);
            } else {
                return new TypePos(
                    ((IFunctionApplication<?>) t).getRootSymbol());
            }
        }

        public TypePos(final IVariable<?> var) {
            this(var, null, null, true);
        }

        public TypePos(final IFunctionSymbol<?> fs) {
            this(null, fs, null, false);
        }

        public TypePos(final IFunctionSymbol<?> fs, final Integer pos) {
            this(null, fs, pos, true);
        }

        private TypePos(final IVariable<?> var, final IFunctionSymbol<?> fs,
                final Integer pos, final boolean input) {

            this.var = var;
            this.fs = fs;
            this.pos = pos;
            this.input = input;
            final int prime = 31;
            int result = 1;
            result = prime * result + ((fs == null) ? 0 : fs.hashCode());
            result = prime * result + (input ? 1231 : 1237);
            result = prime * result + ((pos == null) ? 0 : pos.hashCode());
            result = prime * result + ((var == null) ? 0 : var.hashCode());
            this.hash = result;
        }

        public IFunctionSymbol<?> getFs() {
            return this.fs;
        }

        public Integer getPos() {
            return this.pos;
        }

        public boolean isInput() {
            return this.input;
        }

        public IVariable<?> getVar() {
            return this.var;
        }

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            if (this.var != null) {
                return this.var.export(o);
            } else {
                if (this.input) {
                    return this.fs.export(o) + "/" + this.pos;
                } else {
                    return this.fs.export(o);
                }
            }
        }

        @Override
        public int hashCode() {
            return this.hash;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final TypePos other = (TypePos) obj;
            if (this.fs == null) {
                if (other.fs != null) {
                    return false;
                }
            } else if (!this.fs.equals(other.fs)) {
                return false;
            }
            if (this.input != other.input) {
                return false;
            }
            if (this.pos == null) {
                if (other.pos != null) {
                    return false;
                }
            } else if (!this.pos.equals(other.pos)) {
                return false;
            }
            if (this.var == null) {
                if (other.var != null) {
                    return false;
                }
            } else if (!this.var.equals(other.var)) {
                return false;
            }
            return true;
        }

    }

    private static class BadTypeException extends Exception {

        /**
         *
         */
        private static final long serialVersionUID = 1L;
    }

    public static class TypeInferenceProof extends DefaultProof implements
            IDPExportable {

        final int EXPORT_COLCOUNT = 10;

        private final Map<Set<TypePos>, SemiRingDomain<?>> typeEqClasses;

        public TypeInferenceProof(
                final Map<Set<TypePos>, SemiRingDomain<?>> typeEqClasses) {
            this.typeEqClasses = typeEqClasses;
        }

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, IDPExportable.DEFAULT_LEVEL);
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel verbosityLevel) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, verbosityLevel);
            return sb.toString();
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util o,
            final VerbosityLevel level) {
            for (final Map.Entry<Set<TypePos>, SemiRingDomain<?>> entry : this.typeEqClasses.entrySet()) {
                sb.append("The following variables and function symbol/positions have the domain "
                    + entry.getValue().export(o) + ":");
                sb.append(o.linebreak());
                final Iterator<TypePos> posIter = entry.getKey().iterator();
                sb.append(o.tableStart(this.EXPORT_COLCOUNT));
                final List<String> row = new ArrayList<String>(this.EXPORT_COLCOUNT);
                while (posIter.hasNext()) {
                    final TypePos pos = posIter.next();
                    row.add(pos.export(o));
                    if (row.size() >= this.EXPORT_COLCOUNT) {
                        sb.append(o.tableRow(row));
                        row.clear();
                    }
                }
                if (!row.isEmpty()) {
                    sb.append(o.tableRow(row));
                    row.clear();
                }
                sb.append(o.tableEnd());
                sb.append(o.newline());
            }
        }
    }

}
