package aprove.verification.dpframework.HaskellProblem;

import java.io.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.dpframework.HaskellProblem.Processors.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Input.Annotations.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * HaskellProgram is the result of the Haskell-Translator and
 * it contains all important objects to represent a Haskell program completely.
 * I.e. it contains the modules.
 *
 * @author Stephan Swiderski
 */
public class HaskellProgram extends DefaultBasicObligation
    implements HTML_Able,PLAIN_Able,LaTeX_Able {

    List<Class<? extends HaskellProcessor>> appliedTransformations = new ArrayList<Class<? extends HaskellProcessor>>();

    Modules modules;

    public HaskellProgram() {
        super("HASKELL","HASKELL");
        this.modules = null;
    }

    public HaskellProgram(Modules modules) {
        super("HASKELL","HASKELL");
        this.modules = modules;
    }

    private HaskellProgram(Modules modules, List<Class<? extends HaskellProcessor>> appliedTransformations) {
        this(modules);
        this.appliedTransformations = new ArrayList<Class<? extends HaskellProcessor>>(appliedTransformations);
    }

    /**
     * adds a transformation processor to the set of applied transformations
     * @param transformation the transformation processor that was applied
     */
    public void addTransformation(HaskellProcessor transformation) {
        this.appliedTransformations.add(transformation.getClass());
    }

    @Override
    public HaskellProgram deepcopy() {
        Modules newModules = Copy.deep(this.modules);
        return new HaskellProgram(newModules, this.appliedTransformations);
    }

    @Override
    public String export(Export_Util o) {
         return o.export(this);
    }

    /**
     * @return the transformation processors that were applied to this Haskell Program previously
     */
    public List<Class<? extends HaskellProcessor>> getAppliedTransformations() {
        return this.appliedTransformations;
    }

    /**
     * gets the processors that were applied after the last application of a specific processor
     * @param transformationClass the processor from which on the rest shall be returned
     * @return the list of processors after the specified processor, null if the specified processor was never applied
     */
    public List<Class<? extends HaskellProcessor>> getAppliedTransformationsAfter(
        Class<? extends HaskellProcessor> transformationClass
    ) {
        List<Class<? extends HaskellProcessor>> appliedProcsAfter = new ArrayList<Class<? extends HaskellProcessor>>();
        int idx = this.appliedTransformations.lastIndexOf(transformationClass);
        if (idx < 0) {
            return null;
        }
        for (int i=idx; i < this.appliedTransformations.size(); ++i) {
            appliedProcsAfter.add(this.appliedTransformations.get(i));
        }
        return appliedProcsAfter;
    }

    public Modules getModules() {
        return this.modules;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "H-Termination with start terms");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "hs";
    }

    public boolean isEmpty() {
        return false;
    }

    @Override
    public BasicObligation maybeCopy() {
        return this;
    }

    public void setAnnotation(HaskellAnnotation ha) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Set Annotation: "+ha.getStartTerms());
        }
        if (ha.getStartTerms() != null){
            try {
            (new aprove.input.Programs.haskell.Translator()).translateTermsAndAdd(ha.getStartTerms(),this);
            } catch (Exception e){
            if (Options.isWebInterfaceMode) {
                System.out.println("<h3>Parse Error in Start Terms</h3>");
            }
            System.err.println(e.getMessage());
            e.printStackTrace();
            throw new RuntimeException(e);
            }
        }
        this.modules.onlyReachablesPerStartTerms();
        // TODO what is the effect of the following statement?
        this.modules = Copy.deep(this.modules);
        //HaskellSym.showee(this);
    }

    public HaskellProgram shallowcopy() {
        return new HaskellProgram(this.modules, this.appliedTransformations);
    }

    public Document toBasicDOM() {
        if (this.modules == null) {
            return null;
        }
        return this.modules.toBasicDOM();
    }

    public String toBasicPLAIN() {
        if (this.modules == null) {
            return "";
        }
        StringWriter sw = new StringWriter();
        XMLUtil.transformDocumentPerXSLT(
            this.toBasicDOM(),
            sw,
            XMLUtil.getXSLTReader("Haskell/HaskellProgramToBasicPlain.xsl")
        );
        String res = sw.toString();
        return res;
    }

    public Document toDOM() {
        if (this.modules == null) {
            return null;
        }
        return this.modules.toDOM();
    }

    public Document toFullDOM() {
        if (this.modules == null) {
            return null;
        }
        return this.modules.toFullDOM();
    }

    public String toFullPLAIN() {
        if (this.modules == null) {
            return "";
        }
        StringWriter sw = new StringWriter();
        XMLUtil.transformDocumentPerXSLT(
            this.toFullDOM(),
            sw,
            XMLUtil.getXSLTReader("Haskell/HaskellProgramToPlain.xsl")
        );
        String res = sw.toString();
        return res;
    }

    @Override
    public String toHTML() {
        if (this.modules == null) {
            return "";
        }
        StringWriter sw = new StringWriter();
        XMLUtil.transformDocumentPerXSLT(this.toDOM(),sw,XMLUtil.getXSLTReader("Haskell/HaskellProgramToHTML.xsl"));
        String res = sw.toString();
        return res;
    }

    public String toHTMLFull() {
        if (this.modules == null) {
            return "";
        }
        StringWriter sw = new StringWriter();
        XMLUtil.transformDocumentPerXSLT(this.toFullDOM(),sw,XMLUtil.getXSLTReader("Haskell/HaskellProgramToHTML.xsl"));
        String res = sw.toString();
        return res;
    }

    @Override
    public String toLaTeX() {
        return "Currently LaTeX output for Haskell-Programs not supported";
    }

    @Override
    public String toPLAIN() {
        if (this.modules == null) {
            return "";
        }
        StringWriter sw = new StringWriter();
        XMLUtil.transformDocumentPerXSLT(this.toDOM(),sw,XMLUtil.getXSLTReader("Haskell/HaskellProgramToPlain.xsl"));
        String res = sw.toString();
        return res;
    }

    @Override
    public String toString() {
        return "";
    }

    public String toXML() {
        if (this.modules == null) {
            return "";
        }
        StringWriter sw = new StringWriter();
        XMLUtil.transformDOMtoXML(this.toDOM(),sw);
        String res = sw.toString();
        return res;
    }

    public void updateStartTermsForView(Collection<Pair<HaskellObject,HaskellExp>> sTerms) {
        //this.modules.onlyReachablesPerStartTermsForView(sTerms);
    }

}
