/**
 *
 * @author weidmann
 * @version $Id$
 */
package aprove.input.Programs.srs2;

import java.util.*;

import aprove.*;
import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Input.*;
import immutables.*;

public class ObligationCreator {
    // information provided by class SecondPass
    private Set<Rule> normalRules;
    private Set<Rule> relativeRules;
    private boolean leftmost;
    private boolean rightmost;

    private Language language = null;
    private List<ParseError> obligationErrors;

     // Every possible valid information of the input is coded into a number to the
     // power of 2, so the sum of every valid combination is exactly one integer value.
    public final static int problemConstantNormalRules = 1;
    public final static int problemConstantRelativeRules = 2;
    public final static int problemConstantLeftmost = 4;
    public final static int problemConstantRightmost = 8;

    public ObligationCreator(SecondPass sp){
        this.obligationErrors = new LinkedList<ParseError>();
        this.normalRules = sp.getNormalRules();
        this.relativeRules = sp.getRelativeRules();
        this.leftmost = sp.getLeftmost();
        this.rightmost = sp.getRightmost();
    }

    public BasicObligation buildObligation() {
        /* First, analyze the given combination.
         * For each existing component, add the corresponding integer value
         * and save in a String which components have occured for Error handling.
         * Then, try to find in the case block a valid combination and build
         * the appropriate proof obligation.
         */
        int problemValue = (!this.normalRules.isEmpty() ? ObligationCreator.problemConstantNormalRules : 0 ) |
                           (!this.relativeRules.isEmpty() ? ObligationCreator.problemConstantRelativeRules : 0) |
                           (this.rightmost == true ? ObligationCreator.problemConstantRightmost : 0) |
                           (this.leftmost == true ? ObligationCreator.problemConstantLeftmost : 0) ;

        String problemCombination = (!this.normalRules.isEmpty() ? "Normal Rules, " : "" ) +
                                    (!this.relativeRules.isEmpty() ? "Relative Rules, " : "") +
                                    (this.rightmost == true ? "Rightmost Obligation, ": "") +
                                    (this.leftmost == true ? "Leftmost Obligation, " : "") ;

        if (Globals.DEBUG_WEIDMANN) {
            System.err.println("problemValue: " + problemValue + "  Combination: " + problemCombination);
        }

        switch (problemValue) {
            //problemValue = 1
            case (ObligationCreator.problemConstantNormalRules) : {
                if (Globals.DEBUG_WEIDMANN) {
                    System.err.println("QTRS with empty Q will be created.");
                }
                this.language = Language.QTRS;
                return QTRSProblem.create(ImmutableCreator.create(this.normalRules));
            }
            //problemValue = 2
            case (ObligationCreator.problemConstantRelativeRules) : {
                if (Globals.DEBUG_WEIDMANN) {
                    System.err.println("Rel-TRS with empty R will be created");
                }
                this.language = Language.RTRS;
                return RelTRSProblem.create (
                        ( ImmutableCreator.create(new LinkedHashSet<Rule>()) ) ,
                        ( ImmutableCreator.create(this.relativeRules) )
                );
            }
            //problemValue = 3
            case (ObligationCreator.problemConstantNormalRules + ObligationCreator.problemConstantRelativeRules) : {
                if (Globals.DEBUG_WEIDMANN) {
                    System.err.println("Rel-TRS will be created");
                }
                this.language = Language.RTRS;
                return RelTRSProblem.create (
                        ( ImmutableCreator.create(this.normalRules) ) ,
                        ( ImmutableCreator.create(this.relativeRules) )
                );
            }
            //problemValue = 5
            case (ObligationCreator.problemConstantNormalRules + ObligationCreator.problemConstantLeftmost) : {
                return this.unsupportedCombination(problemCombination);
            }
            //problemValue = 6
            case (ObligationCreator.problemConstantRelativeRules + ObligationCreator.problemConstantLeftmost) : {
                return this.unsupportedCombination(problemCombination);
            }
            //problemValue = 7
            case (ObligationCreator.problemConstantRelativeRules + ObligationCreator.problemConstantNormalRules + ObligationCreator.problemConstantLeftmost) : {
                return this.unsupportedCombination(problemCombination);
            }
            //problemValue = 9
            case (ObligationCreator.problemConstantNormalRules + ObligationCreator.problemConstantRightmost) : {
                if (Globals.DEBUG_WEIDMANN) {
                    System.err.println("QTRS with empty Q and INNERMOST strategy will be created.");
                }
                this.language = Language.QTRS;
                QTRSProblem problem = QTRSProblem.create(
                        ImmutableCreator.create(this.normalRules));
                // STRATEGY RIGHTMOST will be treated as innermost.
                return problem.createInnermost();
            }
            //problemValue = 10
            case (ObligationCreator.problemConstantRelativeRules + ObligationCreator.problemConstantRightmost) : {
                return this.unsupportedCombination(problemCombination);
            }
            //problemValue = 11
            case (ObligationCreator.problemConstantRelativeRules + ObligationCreator.problemConstantNormalRules + ObligationCreator.problemConstantRightmost) : {
                return this.unsupportedCombination(problemCombination);
            }
            case (ObligationCreator.problemConstantLeftmost): // pV = 4
            case (ObligationCreator.problemConstantRightmost): {  // pV = 8
                ParseError pe = new ParseError();
                pe.setMessage("No rules were given, just a "
                        + problemCombination.substring(0, (problemCombination.length()-2)) + "!");
                this.obligationErrors.add(pe);
                return null;
            }
            case 0: { // no rules, no strategy
                ParseError pe = new ParseError();
                pe.setMessage("No rules were given!");
                this.obligationErrors.add(pe);
                return null;
            }

            default : { // pV in {12, 13, 14, 15}, i. e. leftmost and rightmost strategy simultaneously
                ParseError pe = new ParseError();
                pe.setMessage("The combination of "
                        + problemCombination.substring(0, (problemCombination.length()-2))
                        + " is not allowed!");
                this.obligationErrors.add(pe);
                return null;
            }
        }
   }

    private BasicObligation unsupportedCombination(String combination) {
        ParseError pe = new ParseError();
        pe.setMessage("The combination of "
                + combination.substring(0, (combination.length()-2))
                + " is currently not supported!");
        this.obligationErrors.add(pe);
        return null;
    }

    public Language getLanguage() {
        return this.language;
    }

    public List<ParseError> getErrors() {
        return this.obligationErrors;
    }

}
