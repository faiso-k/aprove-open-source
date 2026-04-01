package aprove.verification.oldframework.Algebra.Polynomials;

import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;

/**
 * Small utilities to describe how polynomials should be converted to strings.
 *
 * As implementors will usually be stateless, prefer using the pre-created
 * instances in fields of this interface over instantiating the classes.
 */
public interface PolyFormatter {
    String getMult();
    String getExp();
    String mapVar(String var);

    public class DotAndCaret implements PolyFormatter {
        @Override
        public String getMult() {
            return ".";
        }
        @Override
        public String getExp() {
            return "^";
        }
        @Override
        public String mapVar(String var) {
            return var;
        }
    }

    // This class is not actually stateless,
    // but its state is kept in static variables of CimeFileSearch.
    public class CiME extends DotAndCaret {
        @Override
        public String mapVar(String var) {
            return CimeFileSearch.toVar(var);
        }
    }

    public class Prolog implements PolyFormatter {
        @Override
        public String getMult() {
            return "*";
        }
        @Override
        public String getExp() {
            return null;
        }
        @Override
        public String mapVar(String var) {
            return var;
        }
    }

    // Note the hack in SimplePolyConstraint.toStringRep() !
    PolyFormatter RATSOLVER = new DotAndCaret();

    PolyFormatter MULTISOLVER = new DotAndCaret();

    PolyFormatter CIME = new CiME();

    PolyFormatter PROLOG = new Prolog();
}
