/*
 * Created on Jan 16, 2006
 */
package aprove.verification.dpframework.DPProblem;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Represents an EDP Problem containing an ETRSProblem rWithE, a set of Rules P and a set of Equations eSharp.
 * Assertions check that the Equations of rWithE are only A and C Equations and that eSharp only consists of
 * sharped A and C Equations.
 *
 * @author stein
 * @version $Id$
 */

public final class EDPProblem extends DefaultBasicObligation implements Immutable, HTML_Able, HasTRSTerms {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.DPProblem.EDPProblem");

    /*
     * real values
     */

    private final ImmutableSet<Rule> P;
    private final ImmutableSet<Equation> eSharp;
    private final ETRSProblem rWithE;
    private final boolean minimal;

    /*
     * computes / cached values
     */

    private final EDependencyGraph graph;
    private final int hashCode;
    private ImmutableSet<Rule> usableRules;
    private ImmutableSet<Equation> usableEquations; // usable Equations of E
    private ImmutableSet<Equation> usableESharpEquations; // 1usable Equations of eSharp
    private ImmutableSet<FunctionSymbol> signature;        // signature of rWithE, P and eSharp
    private Boolean isOnlyAnC; //true iff E (of RWithE) only consists of A and C Equations and ESahrp only
                               // contains equations looking like A and C equations converted to sharped rootsymbols.


    /**
     * Creates a new EDPProblem. The eSharpToeMapping is adapted to the E from rWithE.
     */
    private EDPProblem(ImmutableSet<Rule> P, ImmutableSet<Equation> eSharp,
            ETRSProblem rWithE, boolean minimal, EDependencyGraph graph) {
        super("EDP", "E-DP-Problem");
        if (Globals.useAssertions) {
            assert(P != null && eSharp != null && rWithE != null); // perhaps also check whether the graph is valid
        }
        this.P = P;
        this.eSharp = eSharp;
        this.rWithE = rWithE;
        this.minimal = minimal;

        this.graph = graph;
        this.hashCode = 8831123*P.hashCode() + 1293527*rWithE.hashCode() + 36843685*eSharp.hashCode() + (minimal ? 7553901 : 890432841);
        this.usableRules = null;
        this.usableEquations = null;
        this.usableESharpEquations = null;
        this.signature = null;
        this.isOnlyAnC = null;
    }

    /**
     * Creates a new EDPProblem.
     */
    public static EDPProblem create(ImmutableSet<Rule> P, ImmutableSet<Equation> eSharp, ETRSProblem rWithE, boolean minimal) {
        if(Globals.useAssertions) {
            assert(rWithE.checkACandAandC()
                    && EDPProblem.checkESharpIsAnC(eSharp));
        }
        if (Globals.DEBUG_STEIN) {
            EDPProblem.logger.log(Level.INFO, "Getting Equational Dependency Graph\n");
        }
        EDependencyGraph graph = EDependencyGraph.create(P, eSharp, rWithE);
        if (Globals.DEBUG_STEIN) {
            EDPProblem.logger.log(Level.INFO, "Creating new EDP Problem\n");
        }
        return new EDPProblem(P, eSharp, rWithE, minimal, graph);
    }


    /**
     * Returns true iff E (of RWithE) only consists of A and C Equations and ESahrp only
     * contains equations looking like A and C equations converted to sharped rootsymbols.
     */
    public boolean EAndESharpOnlyAnC() {
        if(this.isOnlyAnC == null) {
            this.isOnlyAnC = this.rWithE.checkACandAandC()
            && EDPProblem.checkESharpIsAnC(this.eSharp);
        }
        return this.isOnlyAnC;
    }

    /**
     * returns true iff eSharp only contains equations looking like A and C equations converted to sharped rootsymbols,
     * e.g. only contains equations of the form F(x,f(y,z))==F(f(x,y),z) and F(x,y)==F(y,x)
     */
     private static boolean checkESharpIsAnC(ImmutableSet<Equation> eSharp) {
         for(Equation eq : eSharp) {
             if(eq.getLeft().isVariable() || eq.getRight().isVariable()) {
                 return false;
             }
             FunctionSymbol F = ((TRSFunctionApplication)eq.getLeft()).getRootSymbol();
             if(!((TRSFunctionApplication)eq.getRight()).getRootSymbol().equals(F)) {
                 return false;
             }
             Set<FunctionSymbol> fs = new HashSet<FunctionSymbol>(eq.getFunctionSymbols());
             fs.remove(F);
             if(fs.isEmpty()) {
                 //it must be a C equation
                 TRSVariable x = TRSTerm.createVariable("x");
                 TRSVariable y = TRSTerm.createVariable("y");
                 TRSTerm l = TRSTerm.createFunctionApplication(F, Equation.createArgArrayList(Arrays.asList(x,y)));
                 TRSTerm r = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(y,x)));
                 Equation cEquation = Equation.create(l,r);
                 if(!eq.equals(cEquation)) {
                     return false;
                 }
             }
             else if (fs.size()==1){
                 //it must be a A equation
                 FunctionSymbol f = fs.iterator().next();
                 TRSVariable x = TRSTerm.createVariable("x");
                 TRSVariable y = TRSTerm.createVariable("y");
                 TRSVariable z = TRSTerm.createVariable("z");
                 TRSTerm l = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(
                         TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y))),z)));
                 TRSTerm r = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(
                         x,TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,z))))));
                 Equation aEquation = Equation.create(l,r);
                 if(!eq.equals(aEquation)) {
                     return false;
                 }

             }
             else {
                 //too many FunctionSymbols
                 return false;
             }
         }
         return true;
     }

    /**
     * returns a subproblem with smaller graph
     */
    public EDPProblem getSubProblem(EDependencyGraph graph) {
        return this.getSubProblemWithSmallerP(graph.getP(), graph);
    }

    /**
     * returns a subproblem with smaller P
     */
    public EDPProblem getSubProblemWithSmallerP(ImmutableSet<Rule> P) {
        return this.getSubProblemWithSmallerP(P, this.graph.getSubGraphFromPRules(P));
    }

    /**
     * returns a subproblem with smaller P,
     * the graph and P must have the same nodes
     */
    private EDPProblem getSubProblemWithSmallerP(ImmutableSet<Rule> P, EDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert(graph.getP().equals(P));
            assert (this.P.containsAll(P));
            assert (this.P.size() != P.size());
        }
        ImmutableSet<Equation> eSharp = Options.certifier.isCeta() ? graph.getEsharp() : this.eSharp;

        return new EDPProblem(P, eSharp, this.rWithE, this.minimal, graph);
    }

    public EDPProblem getSubProblemWithSmallerE(ImmutableSet<Equation> E) {
        if (Globals.useAssertions) {
            assert (this.rWithE.getE().containsAll(E));
        }
        ETRSProblem rWithE = this.rWithE.createSubProblemWithSmallerE(E);
        EDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithE);

        return new EDPProblem(this.P, this.eSharp, rWithE, this.minimal, subGraph);
    }

    public EDPProblem getSubProblemWithSmallerR(ImmutableSet<Rule> R) {
        if (Globals.useAssertions) {
            assert (this.rWithE.getR().containsAll(R));
        }
        ETRSProblem rWithE = this.rWithE.createSubProblemWithSmallerR(R);
        EDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithE);

        return new EDPProblem(this.P, this.eSharp, rWithE, this.minimal, subGraph);
    }

    public EDPProblem getSubProblemWithSmallerRandE(ImmutableSet<Rule> R, ImmutableSet<Equation> E) {
        if (Globals.useAssertions) {
            assert (this.rWithE.getR().containsAll(R) && this.rWithE.getE().containsAll(E));
        }
        ETRSProblem rWithE = ETRSProblem.create(R,E);
        EDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithE);

        return new EDPProblem(this.P, this.eSharp, rWithE, this.minimal, subGraph);
    }

    public EDPProblem getSubProblemWithSmallerPandE(ImmutableSet<Rule> P, ImmutableSet<Equation> E) {
        if (Globals.useAssertions) {
            assert (this.rWithE.getE().containsAll(E) && this.P.containsAll(P));
        }
        ETRSProblem rWithE = this.rWithE.createSubProblemWithSmallerE(E);
        EDependencyGraph subGraph = this.graph.getSubGraph(P, rWithE);

        return new EDPProblem(P, this.eSharp, rWithE, this.minimal, subGraph);
    }

    public EDPProblem getSubProblemWithSmallerPandR(ImmutableSet<Rule> P, ImmutableSet<Rule> R) {
        if (Globals.useAssertions) {
            assert (this.rWithE.getR().containsAll(R) && this.P.containsAll(P));
        }
        ETRSProblem rWithE = this.rWithE.createSubProblemWithSmallerR(R);
        EDependencyGraph subGraph = this.graph.getSubGraph(P, rWithE);

        return new EDPProblem(P, this.eSharp, rWithE, this.minimal, subGraph);
    }

    public EDPProblem getSubProblemWithSmallerPandRandE(ImmutableSet<Rule> P, ImmutableSet<Rule> R, ImmutableSet<Equation> E){
        if (Globals.useAssertions) {
            assert (this.rWithE.getR().containsAll(R) && this.rWithE.getE().containsAll(E)
                    && this.P.containsAll(P));
        }
        ETRSProblem rWithE = ETRSProblem.create(R,E);
        EDependencyGraph subGraph = this.graph.getSubGraph(P, rWithE);

        return new EDPProblem(P, this.eSharp, rWithE, this.minimal, subGraph);
    }


    public EDependencyGraph getDependencyGraph() {
        return this.graph;
    }

    public ImmutableSet<Rule> getUsableRules() {
        if (this.usableRules == null) {
            this.usableRules = ImmutableCreator.create(this.rWithE.getEUsableRulesCalculator().getUsableRules(this.P, this.eSharp));
        }
        return this.usableRules;
    }

    /**
     * Returns the usable Equations of E, calculated in EUsableRules.
     */
    public synchronized ImmutableSet<Equation> getUsableEquations() {
        if(this.usableEquations == null) {
            this.usableEquations = ImmutableCreator.create(this.rWithE.getEUsableRulesCalculator().getUsableEquations(this.P, this.eSharp));
        }
        return this.usableEquations;
    }

    public EUsableRules getEUsableRulesCalculator() {
        return this.rWithE.getEUsableRulesCalculator();
    }

    /**
     * Returns the usable Equations os eSharp, calculated in ESharpUsableEquations.
     */
    public synchronized ImmutableSet<Equation> getUsableESharpEquations() {
        if(this.usableESharpEquations == null) {
            this.usableESharpEquations = ImmutableCreator.create(this.rWithE.getESharpUsableEquationsCalculator().getUsableEquations(this.P, this.eSharp));
        }
        return this.usableESharpEquations;
    }

    /**
     * Returns the signature of rWithE, P and eSharp
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.P);
            signature.addAll(CollectionUtils.getFunctionSymbols(this.eSharp));
            signature.addAll(this.rWithE.getSignature());
            this.signature = ImmutableCreator.create(signature);
        }
        return this.signature;
    }

    /**
     * Returns the signature of R and P
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignatureOfRandP() {
        if (this.signature == null) {
            Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.P);
            signature.addAll(this.rWithE.getSignatureOfR());
            this.signature = ImmutableCreator.create(signature);
        }
        return this.signature;
    }

    /**
     * returns the set of all terms in P,E,R,eSharp.
     * the resulting set may be safely modified.
     */
    @Override
    public Set<TRSTerm> getTerms() {
        Set<TRSTerm> terms = CollectionUtils.getTerms(this.P);
        terms.addAll(this.rWithE.getTerms());
        terms.addAll(CollectionUtils.getTerms(this.eSharp));
        return terms;
    }

    public ImmutableSet<Rule> getP() {
        return this.P;
    }

    public boolean getMinimal() {
        return this.minimal;
    }

    public ETRSProblem getRwithE() {
        return this.rWithE;
    }

    public ImmutableSet<Rule> getR() {
        return this.rWithE.getR();
    }

    public ImmutableSet<Equation> getE() {
        return this.rWithE.getE();
    }

    public ImmutableSet<Equation> getESharp() {
        return this.eSharp;
    }

    @Override
    public boolean equals(Object oth) {
        if (this == oth) {
            return true;
        }

        if (oth == null) {
            return false;
        }

        if (oth.getClass() != this.getClass()) {
            return false;
        }

        EDPProblem other = (EDPProblem) oth;

        if (this.minimal != other.minimal) {
            return false;
        }

        if (!this.P.equals(other.P)) {
            return false;
        }

        if(!this.eSharp.equals(other.eSharp)) {
            return false;
        }

        return this.rWithE.equals(other.rWithE);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer s = new StringBuffer();
        if (this.P.isEmpty()) {
            s.append("P is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS P consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.P, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getE().isEmpty()) {
            s.append("E is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set E consists of the following equations:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getE(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getESharp().isEmpty()) {
            s.append("E# is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set E# consists of the following equations:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getESharp(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append(o.export("We have to consider all "+(this.minimal ? "minimal " : "")+"(P,E#,R,E)-chains"));

        //s.append(o.export("The head symbols of this DP problem are "));
        //s.append(o.set(this.getHeadSymbols(), Export_Util.SIMPLESET));

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        throw new UnsupportedOperationException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}

