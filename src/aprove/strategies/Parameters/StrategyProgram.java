package aprove.strategies.Parameters;

import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.exit.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.UserStrategies.*;
import aprove.strategies.Util.*;
import immutables.*;

public class StrategyProgram implements Immutable, Exportable {
    private final static Logger log = Logger.getLogger("aprove.Processors.Parameters.StrategyProgram");

    private final Map<String, UserStrategy> userStrategies;
    private final Map<String, NameDefinition> declarations;
    private final Map<String, String> originalCase;
    final ObjectCreator creator = new ObjectCreator(this);

    /* These two variables change during our lifetime,
     * I'm marking them as transient to illustrate
     * that they are not really part of our state, we are still Immutable.
     */
    private transient List<String> problems;
    private transient String problemNear = null;
    private transient boolean hasParseErrors = false;

    /**
     * Creates a new StrategyProgram from the given names
     */
    public StrategyProgram(Map<String, UserStrategy> program, Map<String, NameDefinition> defaults) {
        this.userStrategies = new LinkedHashMap<String, UserStrategy>();
        this.declarations = new LinkedHashMap<String, NameDefinition>();
        this.originalCase = new LinkedHashMap<String, String>();
        this.putAllIgnoreCase(program, defaults);
    }

    /**
     * Creates a new StrategyProgram from the given names,
     * and from another StrategyProgram to default to for all undefined names.
     */
    public StrategyProgram(StrategyProgram defaults,
            Map<String, UserStrategy> strategies,
            Map<String, NameDefinition> managerInfo) {
        this.userStrategies = new LinkedHashMap<String, UserStrategy>(defaults.userStrategies);
        this.declarations = new LinkedHashMap<String, NameDefinition>(defaults.declarations);
        this.originalCase = new LinkedHashMap<String, String>(defaults.originalCase);
        this.putAllIgnoreCase(strategies, managerInfo);
        this.hasParseErrors = defaults.hasParseErrors;
    }

    private void putAllIgnoreCase(Map<String, UserStrategy> program,
            Map<String, NameDefinition> defaults) {
        for(Map.Entry<String, UserStrategy> e: program.entrySet()) {
            String oldKey = e.getKey();
            String newKey = oldKey.toLowerCase();
            this.userStrategies.put(newKey, e.getValue());
            this.originalCase.put(newKey, oldKey);
        }
        for(Map.Entry<String, NameDefinition> e: defaults.entrySet()) {
            String oldKey = e.getKey();
            String newKey = oldKey.toUpperCase();
            this.declarations.put(newKey, e.getValue());
            this.originalCase.put(newKey, oldKey);
        }
    }

    /** Defunct, but kept to avoid breaking GUI code too badly...
     * @param program unused
     */
    public StrategyProgram(Map<String, UserStrategy> program) {
        throw new UnsupportedOperationException("Don't call me!");
    }

    public UserStrategy lookup(String variable) {
        UserStrategy result = this.userStrategies.get(variable.toLowerCase());
        if (result == null) {
            throw new IllegalArgumentException("Strategy '" + variable + "' is not known!");
        }
        String properName = this.originalCase.get(variable.toLowerCase());
        if (! properName.equals(variable)) {
            StrategyProgram.log.info("Case sensitivity: Consider writing " +
                    properName + " instead of "+variable);
        }
        return result;
    }

    boolean isDeclaredName(String name) {
        return this.declarations.containsKey(name.toUpperCase());
    }

    NameDefinition getDeclaration(String name) throws UserErrorException {
        NameDefinition result = this.declarations.get(name.toUpperCase());
        if (result == null) {
            throw new UserErrorException("No declaration for '" + name + "' known!");
        }
        String properName = this.originalCase.get(name.toUpperCase());
        if (! properName.equals(name)) {
            StrategyProgram.log.info("Case sensitivity: Consider writing " +
                    properName + " instead of "+name);
        }
        return result;
    }

    @Override
    public String export(Export_Util o) {
        throw new UnsupportedOperationException("Don't call me, you blundering fool!");
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Informs this StrategyProgram that there were parse errors
     * and that it should not try to check for semantic errors.
     *
     * If those checks are turned off, this flag is ignored, too.
     */
    void parseError() {
        this.hasParseErrors = true;
    }

    /**
     * Test all known strategy elements in this program for potential problems.
     *
     * @throws KillAproveException
     */
    public void eagerCheck() throws KillAproveException {
        if (this.hasParseErrors) {
            System.err.println("There were errors parsing the strategy, giving up.");
            throw new KillAproveException(2);
        }

        this.problems = new ArrayList<String>();
        for(Map.Entry<String, UserStrategy> e: this.userStrategies.entrySet()) {
            this.problemNear = "strategy expression for " + this.originalCase.get(e.getKey());
            this.maybeCheckEagerly(e.getValue());
        }

        for(Entry<String, NameDefinition> e: this.declarations.entrySet()) {
            this.problemNear = "name declaration for " + this.originalCase.get(e.getKey());
            this.maybeCheckEagerly(e.getValue());
        }

        this.problemNear = null;
        if (! this.problems.isEmpty()) {
            System.err.println(this.problems.size() + " problems in strategy:");
            System.err.println();
            for(String problem: this.problems) {
                System.err.println(problem);
                System.err.println();
            }
            System.err.println("Run with -F to skip error checking and run anyway.");
            throw new KillAproveException(3);
        }
    }

    private void maybeCheckEagerly(Object o) {
        if (! (o instanceof EagerlyCheckable)) {
            return;
        }
        try {
            ((EagerlyCheckable) o).check(this);
        } catch (Exception anything) {
            this.reportProblem("Exception: " + anything.toString());
            anything.printStackTrace();
        }
    }

    public void reportProblem(String problem) {
        if (this.problemNear == null) {
            throw new IllegalStateException("can only report problems during eager check phase!");
        }

        this.problems.add("Problem in " + this.problemNear +":\n" + problem);
    }
}
