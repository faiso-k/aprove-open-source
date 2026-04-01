//Created on 10.11.2004

/**
 * @author patwie
 * @version $Id$
 */

package aprove.input.Programs.cls;

import java.util.*;

import aprove.*;
import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.oldframework.Input.*;
import immutables.*;

public class ObligationCreator {
    /*
     * Declaration of the Constructs to which the parser will
     * collect information.
     */
    private final List<ParseError> obligationErrors;
    private Set<Rule> simpleRules;
    private Set<GeneralizedRule> generalizedRules;
    private Set<ConditionalRule> conditionalRules;
    private Set<ConditionalRule> generalizedConditionalRules;
    private Set<TRSFunctionApplication> initialTerms;
    private Language language = null;

    public ObligationCreator(final FullPass fullpass) {
        this.obligationErrors = new LinkedList<ParseError>();
        this.getAll(fullpass);
    }

    private void getAll(final FullPass fullpass) {
        this.simpleRules = fullpass.getSimpleRules();
        this.generalizedRules = fullpass.getGeneralizedRules();
        this.initialTerms = fullpass.getInitialTerms();
        this.conditionalRules = fullpass.getConditionalRules();
        this.generalizedConditionalRules = fullpass.getGeneralizedConditionalRules();
    }

    private BasicObligation generateProblem() {
        final Set<ConditionalRule> condRules = new LinkedHashSet<ConditionalRule>();
        if (this.conditionalRules != null) {
            condRules.addAll(this.conditionalRules);
        }
        if (this.generalizedConditionalRules != null) {
            condRules.addAll(this.generalizedConditionalRules);
        }
        if (this.simpleRules != null) {
            for (final Rule rule : this.simpleRules) {
                condRules.add(ConditionalRule.create(rule,
                        ImmutableCreator
                        .create(new ArrayList<Condition>())));
            }
        }
        if (this.generalizedRules != null) {
            for (final GeneralizedRule rule : this.generalizedRules) {
                condRules.add(ConditionalRule.create(rule,
                        ImmutableCreator
                        .create(new ArrayList<Condition>())));
            }
        }
        this.language = Language.CLS;
        return CLSProblem.create(condRules, this.initialTerms);
    }

    public BasicObligation buildObligation() {
        final BasicObligation obligation = this.generateProblem();
        if (!this.obligationErrors.isEmpty()) {
            if (Globals.DEBUG_PATWIE) {
                System.err
                        .println("Ich komme aus buildObligation in Klasse ObligationCreator");
                System.err.println(this.obligationErrors.toString());
            }
            return null;
        } else {
            return obligation;
        }
    }

    public Language getLanguage() {
        return this.language;
    }

    public List<ParseError> getErrors() {
        return this.obligationErrors;
    }

}
