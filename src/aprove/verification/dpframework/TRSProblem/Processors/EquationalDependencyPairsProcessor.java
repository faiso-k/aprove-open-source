/*
 * Created on Jan 26, 2006
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Processor which creates out of a given ETRS a new EDPProblem where P contains all dependency pairs of R.
 *
 * @author stein
 * @version $Id$
 */
@NoParams
public class EquationalDependencyPairsProcessor extends ETRSProcessor {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.TRSProblem.Processors.EquationalDependencyPairsProcessor");

    @Override
    protected Result processETRS(ETRSProblem etrs, Abortion aborter) throws AbortionException {
        if(Globals.useAssertions) {
            assert this.isApplicable(etrs);
        }
        EquationalDependencyPairsProcessor.logger.log(Level.FINE, "Getting DPs and ESharp\n");
        Set<Rule> dps = etrs.getDPs();
        Set<Rule> extra_dps = Options.certifier.isCeta() ? etrs.getEDPs() : new HashSet<>(0);        
        Set<Rule> all_dps = new LinkedHashSet<>(dps);
        all_dps.addAll(extra_dps);
        ImmutableSet<Rule> rExt = etrs.getExtR();
        ImmutableSet<Equation> edps = etrs.getESharp();
        ImmutableSet<Equation> E = etrs.getE();
        ImmutableMap<FunctionSymbol, FunctionSymbol> defToTup = etrs.getDefToTupMap();
        EDPProblem edpProblem = EDPProblem.create(ImmutableCreator.create(all_dps), edps, ETRSProblem.create(rExt, E), true);
        return ResultFactory.proved(edpProblem, YNMImplication.EQUIVALENT, 
        		new EquationalDependencyPairsProof(edpProblem, dps, etrs.getExtendedRules(), edps, E, defToTup, extra_dps));
    }

    @Override
    public boolean isETRSApplicable(ETRSProblem etrs) {
        //EDP Problems are only supported for ACnC Equations
        return etrs.checkACandAandC();
    }

    /**
     * Proof which prints out the resulting EDPProblem
     *
     * @author stein
     * @version $Id$
     */
    private class EquationalDependencyPairsProof extends ETRSProof {

	EDPProblem edpProblem;
        Set<Rule> dps;
        Set<Rule> rExt; 
        Set<Equation> edps;
        Set<Equation> E;
        Map<FunctionSymbol, FunctionSymbol> definedToTuple;
        Set<Rule> extra_dps;


	private EquationalDependencyPairsProof(EDPProblem edpProblem,
		Set<Rule> dps, Set<Rule> rExt, Set<Equation> edps, Set<Equation> E,
		Map<FunctionSymbol, FunctionSymbol> defToTup, Set<Rule> extra_dps) {
	    this.edpProblem = edpProblem;
	    this.dps = dps;
	    this.rExt = rExt;
	    this.edps = edps;
	    this.E = E;
	    this.definedToTuple = defToTup;
	    this.extra_dps = extra_dps;
	}
	
	@Override
	public String export(Export_Util eu, VerbosityLevel level){
	    return "Using Dependency Pairs "+eu.cite(new Citation[]{Citation.AG00, Citation.DA_STEIN})+
		    " we result in the following initial EDP problem:"+eu.linebreak()+this.edpProblem.export(eu)+eu.linebreak();
	}
	
        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            final Map<FunctionSymbol, FunctionSymbol> tupleToDefined = new HashMap<>();
            for (final Map.Entry<FunctionSymbol, FunctionSymbol> defToTup : this.definedToTuple.entrySet()) {
                tupleToDefined.put(defToTup.getValue(), defToTup.getKey());
            }
            return DependencyPairsProcessor.adaptMetaData(
                xmlPreMetaData,
                tupleToDefined,
                this.edpProblem.getSignature());
        }


	@Override
	public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlPreMetaData, final CPFModus modus) {
	    if (!this.isCPFCheckableProof(modus)) {
		return super.toCPF(doc, childrenProofs, xmlPreMetaData, modus);
	    }
	    final XMLMetaData xmlMetaData = this.adaptMetaData(xmlPreMetaData);
	    Set<Equation> ac_dps = new LinkedHashSet<>(this.edps);
	    for (Rule rule : extra_dps) {
		ac_dps.add(Equation.create(rule.getLeft(), rule.getRight()));
	    }
	    return CPFTag.AC_TERMINATION_PROOF.create(doc,
		    CPFTag.AC_DP_TRANS.create(doc,
			    CPFTag.EQUATIONS.create(doc, CPFTag.equationRules(doc, xmlMetaData, this.E)),
			    CPFTag.DP_EQUATIONS.create(doc, CPFTag.equationRules(doc, xmlMetaData, ac_dps)),
			    CPFTag.dps(doc, xmlMetaData, this.dps),
			    CPFTag.DP_EXTENSIONS.create(doc, CPFTag.rules(doc, xmlMetaData, this.rExt)),
			    childrenProofs[0]));
	}

	@Override
	public String getNonCPFExportableReason(CPFModus modus) {
	    return super.getNonCPFExportableReason(modus);
	}


	@Override
	public boolean isCPFCheckableProof(final CPFModus modus) {
	    return modus.isPositive();
	}

    }
}
