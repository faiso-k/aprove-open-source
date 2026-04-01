package aprove.verification.theoremprover.TerminationProofs;

import java.util.*;

import aprove.input.Utility.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Input.*;

/**
 * This proof class collects and outputs parse errors.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class ParserErrorsSourceExceptionProof extends Proof {

    ParseErrors errors;

    public ParserErrorsSourceExceptionProof(ParseErrors errors, Input input) {
        super();
        this.errors = errors;
        this.name = "Parser Error";
        this.shortName = "Parser Error";
        this.longName = "Parser Error";
    }

    @Override
    public String export(Export_Util o) {
        if (Proof.CACHE_VALUES) {
                if (this.result.length() != 0) {
                    return this.result.toString();
                }
        } else {
            this.startUp();
        }

        this.result.append("Error(s) parsing the given input file:\n");
        this.result.append(o.linebreak());
        this.result.append(o.linebreak());
        Iterator i = this.errors.iterator();
        while (i.hasNext()) {
            ParseError error = (ParseError)i.next();
            this.result.append(o.verb(o.export(error)));
            this.result.append(o.linebreak());
        }
        return this.result.toString();
    }

    public String toBibTeX() {
        return "";
    }

}
