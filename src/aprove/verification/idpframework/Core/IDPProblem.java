package aprove.verification.idpframework.Core;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Profiling.*;
import aprove.verification.oldframework.Utility.Profiling.FeaturesIDP.*;
import aprove.xml.*;
import immutables.*;

/**
 * Integer DP problem.
 * @author mpluecke
 * @version $Id$
 */
public abstract class IDPProblem extends DefaultBasicObligation implements
        Immutable, HTML_Able, XMLObligationExportable, DOT_Able, IDPExportable,
        HasFeatureVector<FeaturesIDP.Features>,
        SelfMarkable<Conjunction<IDPProblem>, IDPProblem>
{

    /**
     * IDependencyGraph
     */
    protected final IDependencyGraph idpGraph;

    /**
     * Marks for IDP problem.
     */
    private final MarksHandler<Conjunction<IDPProblem>, IDPProblem, IDPProblem> marks;

    /**
     * computed on the fly
     */

    protected final Integer idpId;

    protected static Integer currentIDPId = 0;

    protected IDPProblem(final IDependencyGraph idpGraph) {
        this("IDP", "Integer DP Problem", idpGraph);
    }

    protected IDPProblem(final String shortName, final String longName, final IDependencyGraph idpGraph) {
        super(shortName, longName);
        synchronized (IDPProblem.class) {
            this.idpId = IDPProblem.currentIDPId++;
        }
        this.marks = new MarksHandler<Conjunction<IDPProblem>, IDPProblem, IDPProblem>(this);
        this.idpGraph = idpGraph;

        if (Globals.useAssertions) {
            final Map<Pair<String, Integer>, IFunctionSymbol<?>> usedNames =
                new HashMap<Pair<String, Integer>, IFunctionSymbol<?>>();
            for (final IFunctionSymbol<?> fs : idpGraph.getFunctionSymbols()) {
                final IFunctionSymbol<?> old =
                    usedNames.put(new Pair<String, Integer>(fs.getName(),
                        fs.getArity()), fs);
                assert old == null || old.equals(fs) : "name / arity clash for function symbol: "
                    + fs.getName() + " / " + fs.getArity();
            }
            final Set<String> usedVarNames = new HashSet<String>();
            for (final IVariable<?> var : idpGraph.getVariables()) {
                assert (usedVarNames.add(var.getName())) : "name clash for variable (inconsistend domains): "
                    + var.getName();
            }
        }
    }

    @Override
    public FeatureVector<Features> getFeatureVector() {
        return null;
    }

    public IDependencyGraph getIdpGraph() {
        return this.idpGraph;
    }

    public ItpfFactory getItpfFactory() {
        return this.idpGraph.getItpfFactory();
    }

    @Override
    public MarksHandler<Conjunction<IDPProblem>, IDPProblem, IDPProblem> getMarks() {
        return this.marks;
    }

    public abstract IDPProblem change(final IDependencyGraph idpGraph);

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
        final VerbosityLevel verbosityLevel) {
//        try {
//            final BufferedWriter out =
//                new BufferedWriter(new FileWriter("./idp" + (idpId) + ".dot"));
//            out.write(idpGraph.toDOT(subGraphs));
//            out.close();
//        } catch (final FileNotFoundException e) {
//            e.printStackTrace();
//        } catch (final IOException e) {
//            e.printStackTrace();
//        }
        sb.append(o.export("IDP problem:"));
        sb.append(o.cond_linebreak());
        sb.append("The following function symbols are pre-defined:");
        sb.append(o.cond_linebreak());
        sb.append(this.idpGraph.getPredefinedMap().export(o));
        sb.append(o.cond_linebreak());
        sb.append(o.cond_linebreak());

        this.exportTypes(sb, o, verbosityLevel);

        sb.append(o.cond_linebreak());

        this.exportIdpGraph(sb, o, verbosityLevel);
    }

    private void exportTypes(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
        sb.append("The function symbols and variables have the following type:");
        sb.append(o.cond_linebreak());
        final CollectionMap<List<Domain>, IFunctionSymbol<?>> functionDomains =
            this.getFunctionDomains(this.idpGraph.getVariables());

        sb.append(o.tableStart(3));

        for (final Map.Entry<List<Domain>, Collection<IFunctionSymbol<?>>> domainSet : functionDomains.entrySet()) {
            final ArrayList<String> row = new ArrayList<String>(2);

            final StringBuilder domainSb = new StringBuilder();
            final Iterator<Domain> domIter =
                domainSet.getKey().iterator();

            while (domIter.hasNext()) {
                final Domain domain = domIter.next();
                domain.export(domainSb, o, verbosityLevel);
                if (domIter.hasNext()) {
                    domainSb.append(" ");
                    domainSb.append(o.rightarrow());
                    domainSb.append(" ");
                }
            }
            row.add(domainSb.toString());

            row.add(":");
            row.add(o.set(domainSet.getValue(), Export_Util.NICE_SET));
            sb.append(o.tableRow(row));
        }


        final CollectionMap<Domain, IVariable<?>> variableDomains =
            this.getVariableDomains(this.idpGraph.getVariables());


        for (final Map.Entry<Domain, Collection<IVariable<?>>> domainSet : variableDomains.entrySet()) {
            final ArrayList<String> row = new ArrayList<String>(2);
            row.add(domainSet.getKey().export(o, verbosityLevel));
            row.add(":");
            row.add(o.set(domainSet.getValue(), Export_Util.NICE_SET));
            sb.append(o.tableRow(row));
        }

        sb.append(o.tableEnd());
        sb.append(o.cond_linebreak());
    }

    private CollectionMap<List<Domain>, IFunctionSymbol<?>> getFunctionDomains(final ImmutableSet<IVariable<?>> variables) {
        final CollectionMap<List<Domain>, IFunctionSymbol<?>> res =
            new CollectionMap<List<Domain>, IFunctionSymbol<?>>();

        for (final IFunctionSymbol<?> fs : this.idpGraph.getFunctionSymbols()) {
            final List<Domain> doms = new ArrayList<Domain>(fs.getDomains());
            doms.add(fs.getResultDomain());

            res.add(doms, fs);
        }

        return res;
    }

    private CollectionMap<Domain, IVariable<?>> getVariableDomains(final ImmutableSet<IVariable<?>> variables) {
        final CollectionMap<Domain, IVariable<?>> res =
            new CollectionMap<Domain, IVariable<?>>();
        for (final IVariable<?> variable : variables) {
            res.add(variable.getDomain(), variable);
        }
        return res;
    }

    private void exportIdpGraph(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        if (this.idpGraph.getNodes().isEmpty()) {
            sb.append("The integer pair graph is empty.");
            sb.append(o.cond_linebreak());
        } else {
            sb.append(o.export("The integer pair graph contains the following rules and edges:"));
            sb.append(o.cond_linebreak());
            this.idpGraph.export(sb, o, verbosityLevel);
            sb.append(o.cond_linebreak());

        }
    }

    public String externName() {
        return "idp";
    }

    /**
     * Convenience method.
     * @return
     */
    public IDPPredefinedMap getPredefinedMap() {
        return this.idpGraph.getPredefinedMap();
    }

    public PolyInterpretation<?> getPolyInterpretation() {
        return this.idpGraph.getPolyInterpretation();
    }

    public PolyFactory getPolyFactory() {
        final PolyInterpretation<?> polyInterpretation = this.getPolyInterpretation();
        return polyInterpretation != null ? polyInterpretation.getFactory() : null;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Finiteness");
    }

    @Override
    public abstract String toDOT();

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public Conjunction<IDPProblem> getSelfMark() {
        return new Conjunction<IDPProblem>(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "idpv2";
    }
}
