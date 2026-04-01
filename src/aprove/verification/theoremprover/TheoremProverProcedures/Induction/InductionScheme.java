package aprove.verification.theoremprover.TheoremProverProcedures.Induction;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * A class for an induction scheme
 *
 * @author dickmeis
 * @version $Id$
 */

public class InductionScheme implements Exportable, HTML_Able, PLAIN_Able, LaTeX_Able{

    private boolean DEBUG_MERGE = Globals.DEBUG_DICKMEIS && false;

    private List<InductionSchemeComponent> inductionSchemeComponents;

    public InductionScheme(List<InductionSchemeComponent> inductionSchemeComponents){
        this.inductionSchemeComponents = inductionSchemeComponents;
    }

    public List<InductionSchemeComponent> getInductionSchemeComponents(){
        return this.inductionSchemeComponents;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        for (InductionSchemeComponent isc : this.inductionSchemeComponents) {
            sb.append(isc);
            sb.append("\n");
        }
        return sb.toString();
    }

    /**
     * Merges this with the given induction scheme and returns its outcome.
     *
     * @param is2 the induction scheme to merge with
     * @param useLA whether LA should be used
     * @return the merged induction scheme
     */
    public InductionScheme merge(InductionScheme is2, boolean useLA, LAProgramProperties laProgram, List<AlgebraVariable> variableOrdering) {
        List<InductionSchemeComponent> newInductionSchemeComponents = new ArrayList<InductionSchemeComponent>();
        InductionSchemeComponent isc;

        int i = 0;
        for (InductionSchemeComponent isc1 : this.inductionSchemeComponents) {
            int j=0;
            for (InductionSchemeComponent isc2 : is2.inductionSchemeComponents) {

                if(this.DEBUG_MERGE && i==3 && j==3){
                    System.out.println("breakpoint");
                }

                isc = isc1.merge(isc2, useLA, laProgram, variableOrdering);

                if(this.DEBUG_MERGE){
                    System.out.println("(" + i + "," + j + ")");
                    System.out.println(isc1 + "\n");
                    System.out.println(isc2 + "\n");
                    System.out.println("Resulting in:\n" +isc + "\n");
                    System.out.println("\n\n\n");
                }

                if (isc != null){
                    newInductionSchemeComponents.add(isc);
                }

                j++;

            }
            i++;
        }

        return new InductionScheme(newInductionSchemeComponents);
    }

    public InductionScheme deepcopy() {
        ArrayList<InductionSchemeComponent> newInductionSchemeComponents =
            new ArrayList<InductionSchemeComponent>(this.inductionSchemeComponents.size());

        for (InductionSchemeComponent component : this.inductionSchemeComponents) {
            newInductionSchemeComponents.add(component.deepcopy());
        }

        return new InductionScheme(newInductionSchemeComponents);
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();

        sb.append(o.set(this.inductionSchemeComponents, 3));

        return sb.toString();
    }

    @Override
    public String toLaTeX() {
        return this.export(new LaTeX_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }
}