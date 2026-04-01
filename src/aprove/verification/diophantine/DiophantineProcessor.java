package aprove.verification.diophantine;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * This diophantine "processor" solves a set of Diophantine constraints.
 * It is also used by DiophantineSolver as an argument source
 * by the rather ugly EngineHack.
 *
 * @author Patrick Kabasci, Peter Schneider-Kamp
 * @version $Id$
 */
public class DiophantineProcessor extends Processor.ProcessorSkeleton {

    private final Engine engine;

    private final DiophantineSATConverter satConverter;

    private final SimplificationMode simplification;
    private final boolean stripExponents;
    private BigInteger range;

    @ParamsViaArgumentObject
    public DiophantineProcessor(Arguments arguments) {
        this.engine = arguments.engine;
        this.satConverter = arguments.satConverter;
        this.simplification = arguments.simplification;
        this.stripExponents = arguments.stripExponents;
        this.range = BigInteger.valueOf(arguments.range);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof DiophantineConstraints;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        DiophantineConstraints constraints = (DiophantineConstraints) obl;

        DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.getRange());

        Engine engine = this.getEngine();
        SearchAlgorithm searchAlg;
        // first take the search algorithm from the engine
        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            searchAlg = ((SatEngine)engine).getSearchAlgorithm(allRanges, this.getSatConverter());
        }
        else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        // now wrap the Engine's search algorithm into the simplifying search
        searchAlg = SimplifyingSearch.create(searchAlg, true, this.getStripExponents(), this.getSimplification());

        Set<SimplePolyConstraint> constraintSet = new LinkedHashSet<SimplePolyConstraint>(constraints.getConstraints());
        Map<String, BigInteger> retMap = searchAlg.search(constraintSet, new LinkedHashSet<SimplePolyConstraint> (), aborter);
        if (retMap != null && searchAlg.introducesFreshVariables()) {
            Set<String> inputIndefs = SimplePolyConstraint.getIndefinites(constraintSet);
            retMap.keySet().retainAll(inputIndefs);
        }
        Proof proof = new DiophantineProof(retMap);
        if (retMap != null) {
            return ResultFactory.proved(proof);
        } else {
            return ResultFactory.disproved(proof);
        }
    }

    public Engine getEngine() {
        return this.engine;
    }

    public DiophantineSATConverter getSatConverter() {
        return this.satConverter;
    }

    /**
     * @return the simplification
     */
    public SimplificationMode getSimplification() {
        return this.simplification;
    }

    /**
     * @return the stripExponents
     */
    public boolean getStripExponents() {
        return this.stripExponents;
    }

    public BigInteger getRange() {
        return this.range;
    }

    public static class Arguments {
        public Engine engine;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean stripExponents;
        public int range = 1;
    }

    public class DiophantineProof extends Proof.DefaultProof {

        private Map<String, BigInteger> solution;

        public DiophantineProof(Map<String, BigInteger> solution) {
            this.solution = solution;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            if (this.solution == null) {
                return "No solution in the given range.";
            }
            StringBuilder sb = new StringBuilder();
            sb.append("Solution:");
            for (Map.Entry<String, BigInteger> entry : this.solution.entrySet()) {
                sb.append(o.newline());
                sb.append(entry.getKey());
                sb.append(o.appSpace());
                sb.append(o.eqSign());
                sb.append(o.appSpace());
                sb.append(entry.getValue());
            }
            return sb.toString();
        }

        @Override
        public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
            // not regarding any XMLMetaData because in this knot it's no more needed in any case
            if (this.solution == null) {
                return XMLTag.DIO_NO_SOLUTION.createElement(doc);
            }
            Element solTag = XMLTag.DIO_SOLUTION.createElement(doc);
            for (Map.Entry<String, BigInteger> entry : this.solution.entrySet()) {
                Element variableTag = XMLTag.createIdentifier(doc, entry.getKey());
                Element valueTag = XMLTag.createInteger(doc, entry.getValue().toString());
                Element mappingTag = XMLTag.DIO_ASSIGNMENT.createElement(doc);
                mappingTag.appendChild(variableTag);
                mappingTag.appendChild(valueTag);
                solTag.appendChild(mappingTag);
            }
            return solTag;
        }

        public String toCime() {
            if (this.solution == null) {
                return "+NO solution.\n";
            }
            StringBuilder sb = new StringBuilder();
            sb.append ("+SOLUTION:\n");
            for (Map.Entry<String, BigInteger> entry: this.solution.entrySet()) {
                sb.append("+ ");
                sb.append(entry.getKey());
                sb.append(" = ");
                sb.append(entry.getValue());
                sb.append("\n");
            }
            sb.append("-\n");
            return sb.toString();
        }

    }

}

