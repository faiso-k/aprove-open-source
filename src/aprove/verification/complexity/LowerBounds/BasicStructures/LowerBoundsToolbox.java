package aprove.verification.complexity.LowerBounds.BasicStructures;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.*;
import aprove.verification.complexity.LowerBounds.EquationalUnification.*;
import aprove.verification.complexity.LowerBounds.GeneratorEquations.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;


public class LowerBoundsToolbox {

    public final EquationalUnifier unifier;
    public final TRSVariable inductionVar;
    public final TRSFunctionApplication inductionCons;
    public final PFHelper pfHelper;
    public final Abortion aborter;
    public final TermGenerator termGenerator;
    public final GeneratorEquations generatorEquations;
    public final LowerBoundsTrs trs;
    public final RenamingCentral renamingCentral;
    public final FunctionSymbol toAnalyze;
    public final TRSFunctionApplication arbitraryTerm;
    public final GeneratorEquationRewriter genEqRewriter;
    public final TrsTypes types;

    public LowerBoundsToolbox(OrderedCpxTrsLowerBoundsProblem cpxObl, Abortion aborter) {
        this.aborter = aborter;
        this.trs = cpxObl.getTrs().clone();
        this.types = this.trs.getTypes();
        this.renamingCentral = cpxObl.getRenamingCentral();
        this.inductionVar = this.renamingCentral.freshVariable("n");
        this.inductionCons = TRSTerm.createFunctionApplication(this.renamingCentral.freshConstant("c"));
        this.types.declare(this.inductionCons.getRootSymbol(), FunctionSymbolSimpleType.Nats);
        this.pfHelper = new PFHelper(this.types);
        this.generatorEquations = cpxObl.getGeneratorEquations();
        this.termGenerator = this.generatorEquations.getTermGenerator();
        this.unifier = new EquationalUnifier(this.generatorEquations, this.renamingCentral, this.types, this.termGenerator);
        this.toAnalyze = cpxObl.getCurrent();
        this.arbitraryTerm = cpxObl.getArbitraryTerm();
        this.genEqRewriter = new GeneratorEquationRewriter(this.generatorEquations, this.pfHelper, this.unifier);
    }

}
