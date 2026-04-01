package aprove.verification.oldframework.IntTRS.InvariantGen;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import org.antlr.runtime.*;

import aprove.*;
import aprove.input.Generated.InterprocInvariant.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class AddInterprocInvariantsProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti
    ) throws AbortionException {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final ImmutableSet<IGeneralizedRule> rules = problem.getRules();
        final Map<FunctionSymbol, TRSFunctionApplication> fsToInvariantMap;
        if (problem.getStartTerm() != null) {
            fsToInvariantMap =
                AddInterprocInvariantsProcessor.callInterproc(
                    rules,
                    Collections.singleton(problem.getStartTerm().getRootSymbol()),
                    aborter
                );
        } else {
            fsToInvariantMap =
                AddInterprocInvariantsProcessor.callInterproc(
                    rules,
                    Collections.<FunctionSymbol>emptySet(),
                    aborter
                );
        }

        if (fsToInvariantMap.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (final IGeneralizedRule oldRule : rules) {
            final FunctionSymbol definedSym = oldRule.getRootSymbol();
            final TRSTerm invTerm = fsToInvariantMap.get(definedSym);
            if (invTerm == null) {
                newRules.add(oldRule);
                continue;
            }

            /*
             * OK, the invariant might use other variables. However, the variables in the invariant are canonical
             * (x1 ... xn) and we build a substitution to their new values here:
             */
            final Map<TRSVariable, TRSTerm> substMap = new LinkedHashMap<>();
            int argNum = 0;
            for (final TRSTerm arg : oldRule.getLeft().getArguments()) {
                substMap.put(TRSTerm.createVariable("x" + argNum), arg);
                argNum++;
            }
            final TRSTerm newInvTerm = invTerm.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(substMap)));
            final TRSTerm newCond = IDPv2ToIDPv1Utilities.getConjunction(oldRule.getCondTerm(), newInvTerm);
            newRules.add(IGeneralizedRule.create(oldRule.getLeft(), oldRule.getRight(), newCond));
        }

        return ResultFactory.proved(
            new IRSProblem(ImmutableCreator.create(newRules), problem.getStartTerm()),
            YNMImplication.EQUIVALENT,
            new AddInterprocInvariantsProof(fsToInvariantMap));
    }

    /**
     * (1) Generate program from intTRS
     * (2) Call Interproc
     * (3) Parse invariants from interproc and return
     * @param rules the rules for our system (no COM_1 crap, please)
     * @param set the start symbol, if there is one (null otherwise)
     * @param aborter our friend, the aborter. It aborts stuff.
     * @throws AbortionException when aborted
     */
    public static Map<FunctionSymbol, TRSFunctionApplication> callInterproc(
        final Set<IGeneralizedRule> rules,
        final Set<FunctionSymbol> startSyms,
        final Abortion aborter) throws AbortionException
    {
        final StringBuilder programSB = new StringBuilder();
        AddInterprocInvariantsProcessor.buildInterprocDefinitionsForRules(rules, programSB);
        AddInterprocInvariantsProcessor.buildInterprocMain(startSyms, programSB);

        final Process process;
        File input = null;
        Scanner sc = null;
        Scanner errors = null;
        final Map<FunctionSymbol, TRSFunctionApplication> fsToInvariantMap = new LinkedHashMap<>();
        try {
            //Write our data:
            aborter.checkAbortion();
            input = File.createTempFile("APRoVEExternal", ".interproc");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(programSB.toString());
            inputWriter.close();
            aborter.checkAbortion();

            //Call Interproc
            final ArrayList<String> parameters = new ArrayList<>();
            parameters.add("interproc");
            parameters.add("-display");
            parameters.add("text");
            parameters.add(input.getCanonicalPath());
            final ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[parameters.size()]));
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            try {
                process.waitFor();
            } catch (final InterruptedException e) {
                assert false : "Interproc interrupted!";
            }

            //Parse output
            errors = new Scanner(new BufferedInputStream(process.getErrorStream()));
            while (errors.hasNextLine()) {
                System.err.println("Interproc stderr: " + errors.nextLine());
            }
            errors.close();

            sc = new Scanner(new BufferedInputStream(process.getInputStream()));
            while (sc.hasNextLine()) {
                String line = sc.nextLine();
                if (!line.startsWith("proc ")) {
                    continue;
                }
                //Line is "proc f_n (arguments)", where f is a function symbol name and n is the arity
                String[] splittedLine = line.split(" ");
                final String fSymPlusArity = splittedLine[1];
                final int splitPos = fSymPlusArity.lastIndexOf('_');
                final String fSymName = fSymPlusArity.substring(0, splitPos);
                final int fSymArity = Integer.parseInt(fSymPlusArity.substring(splitPos + 1));
                final FunctionSymbol defSym = FunctionSymbol.create(fSymName, fSymArity);

                //Continue until finding the line "  /* (L$Line C$Char) [| INV
                while (sc.hasNextLine()) {
                    line = sc.nextLine();
                    if (!line.startsWith("  /* ")) {
                        continue;
                    }

                    //Found no invariant
                    if (!line.contains("[|")) {
                        break;
                    }

                    splittedLine = line.split("\\|");
                    final StringBuilder sb = new StringBuilder();
                    sb.append(splittedLine[1]);

                    //Check if we are not done yet. If it was splitted over several lines, continue reading:
                    if (!line.contains("|]")) {
                        while (sc.hasNextLine()) {
                            line = sc.nextLine();
                            if (line.contains("|]")) {
                                splittedLine = line.split("\\|");
                                sb.append(splittedLine[0]);
                                break;
                            } else {
                                sb.append(line);
                            }
                        }
                    }

                    final String invString = sb.toString();

                    final InterprocInvariantLexer lex = new InterprocInvariantLexer(new ANTLRStringStream(invString));
                    final CommonTokenStream tokens = new CommonTokenStream(lex);
                    final InterprocInvariantParser parser = new InterprocInvariantParser(tokens);
                    TRSFunctionApplication invTerm;
                    try {
                        invTerm = (TRSFunctionApplication) parser.interprocInvariant();
                    } catch (final RecognitionException e) {
                        break;
                    }

                    fsToInvariantMap.put(defSym, invTerm);
                    break;
                }
            }
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (sc != null) {
                sc.close();
            }
            if (errors != null) {
                errors.close();
            }
        }

        return fsToInvariantMap;
    }

    private static void buildInterprocMain(final Set<FunctionSymbol> startSyms, final StringBuilder programSB) {
        final Set<TRSVariable> vars = new LinkedHashSet<>();

        for (final FunctionSymbol startSym : startSyms) {
            for (int i = 0; i < startSym.getArity(); i++) {
                vars.add(TRSTerm.createVariable(startSym.toString() + "_" + i));
            }
        }

        if (!vars.isEmpty()) {
            programSB.append("\nvar ");
            boolean isFirst = true;
            for (final TRSVariable var : vars) {
                if (!isFirst) {
                    programSB.append(", ");
                }
                isFirst = false;
                programSB.append(var.toString()).append(":int");
            }
            programSB.append(";\n");
        }
        programSB.append("begin\n");

        for (final FunctionSymbol startSym : startSyms) {
            for (int i = 0; i < startSym.getArity(); i++) {
                programSB.append(startSym.toString()).append("_" + i).append(" = random;\n");
            }
            programSB.append("() = ").append(startSym.toString()).append("(");
            for (int i = 0; i < startSym.getArity(); i++) {
                if (i > 0) {
                    programSB.append(", ");
                }
                programSB.append(startSym.toString()).append("_" + i);
            }
            programSB.append(");\n");
        }
        programSB.append("\nend\n");
    }

    /**
     * Builds an interproc-compatible program from a given set of intTRS rules, preparing for external
     * invariant generation.
     * @param rules a set of intTRS rules
     * @param programSB a string builder in which the program will be placed
     */
    private static void buildInterprocDefinitionsForRules(
        final Set<IGeneralizedRule> rules,
        final StringBuilder programSB)
    {
        final CollectionMap<FunctionSymbol, IGeneralizedRule> fsToDefRules = new CollectionMap<>();

        for (final IGeneralizedRule iRule : rules) {
            fsToDefRules.add(iRule.getRootSymbol(), iRule);
        }

        for (final Map.Entry<FunctionSymbol, Collection<IGeneralizedRule>> e : fsToDefRules.entrySet()) {
            AddInterprocInvariantsProcessor.buildInterprocProcForSymbol(
                fsToDefRules.keySet(),
                e.getKey(),
                e.getValue(),
                programSB
            );
        }
    }

    /**
     * Build an Interproc procedure for a set of rules defining the symbol f, looking like that:
     *  f(x1, ..., xn) -> g1(t1.1, ..., t1.k_1) | c1
     *  ...
     *  f(x1, ..., xn) -> gm(tm.1, ..., tm.k_m) | cm,
     * We generate a procedure of the form
     * proc f (x1:int, ..., xn:int) returns ()
     * var
     *  randChoice:int,
     *  v1.1:int, ..., v1.k_1:int
     *  ...
     *  vm.1:int, ..., vm.k_m:int;
     * begin
     *   randChoice = random;
     *   if (randChoice == 1) then
     *    if (c1) then
     *      v1.1 = t1.1;
     *      ...
     *      v1.k_1 = t1.k_1;
     *      () = g1(v1.1, ..., v1.k_1);
     *    endif;
     *   endif;
     *   ...
     *   if (randChoice == m) then
     *    if (cm) then
     *    endif;
     *   endif;
     * end
     * @param definedSymbols all defined symbols
     * @param definedSym the symbol defined
     * @param definingRules the rules defining the symbol
     * @param programSB the string builder into which we dump the definition
     */
    private static void buildInterprocProcForSymbol(
        final Set<FunctionSymbol> definedSymbols,
        final FunctionSymbol definedSym,
        final Collection<IGeneralizedRule> definingRules,
        final StringBuilder programSB)
    {
        //Step one: Creating all the variables for the arguments on the rhs:
        final Map<IGeneralizedRule, Pair<TRSSubstitution, List<Pair<TRSVariable, TRSTerm>>>> ruleToArgVarMap =
            new LinkedHashMap<>();
        final Collection<TRSVariable> variables = new LinkedHashSet<>();
        int ruleNumber = 0;
        for (final IGeneralizedRule rule : definingRules) {
            ruleNumber++;
            final IGeneralizedRule normalizedRule = rule.getWithRenumberedVariables("x");
            final Collection<TRSVariable> boundVars = normalizedRule.getLeft().getVariables();
            final TRSTerm right = normalizedRule.getRight();

            final List<Pair<TRSVariable, TRSTerm>> argVarsAndTerms = new LinkedList<>();
            TRSSubstitution freshVarSubst = TRSSubstitution.EMPTY_SUBSTITUTION;
            if (!right.isVariable()) {

                //Generate fresh names for the new, unbound variables:
                int freshVarNum = 0;
                final Set<TRSVariable> usedVars = right.getVariables();
                if (normalizedRule.getCondTerm() != null) {
                    usedVars.addAll(normalizedRule.getCondTerm().getVariables());
                }
                for (final TRSVariable varUsedOnRight : usedVars) {
                    //Variable is bound or already handled:
                    if (boundVars.contains(varUsedOnRight) || freshVarSubst.getDomain().contains(varUsedOnRight)) {
                        continue;
                    }

                    //Get a new name
                    freshVarNum++;
                    final TRSVariable freshVar = TRSTerm.createVariable("v_" + ruleNumber + "_fresh_" + freshVarNum);
                    variables.add(freshVar);
                    freshVarSubst = freshVarSubst.compose(TRSSubstitution.create(varUsedOnRight, freshVar));
                }

                int argNumber = 0;
                for (final TRSTerm arg : ((TRSFunctionApplication) right).getArguments()) {
                    argNumber++;

                    final TRSVariable newVar = TRSTerm.createVariable("v_" + ruleNumber + "_" + argNumber);
                    argVarsAndTerms.add(new Pair<>(newVar, arg.applySubstitution(freshVarSubst)));
                    variables.add(newVar);
                }
            }
            ruleToArgVarMap.put(normalizedRule, new Pair<>(freshVarSubst, argVarsAndTerms));
        }

        //Step two: Build the proc:
        programSB.append("proc ").append(definedSym.toString()).append(" (");
        for (int i = 0; i < definedSym.getArity(); i++) {
            if (i > 0) {
                programSB.append(", ");
            }
            programSB.append("x").append(Integer.toString(i)).append(":int");
        }
        programSB.append(") returns ()\nvar randomChoice:int");
        for (final TRSVariable var : variables) {
            programSB.append(", ").append(var.toString()).append(":int");
        }
        programSB.append(";\nbegin\nrandomChoice = random;\n");

        ruleNumber = 0;
        for (final Entry<IGeneralizedRule, Pair<TRSSubstitution, List<Pair<TRSVariable, TRSTerm>>>> e : ruleToArgVarMap
            .entrySet())
        {
            final IGeneralizedRule rule = e.getKey();
            final TRSTerm right = rule.getRight();
            if (right.isVariable()) {
                continue;
            }
            final FunctionSymbol calledSym = ((TRSFunctionApplication) right).getRootSymbol();
            ruleNumber++;
            if (!definedSymbols.contains(calledSym)) {
                if (Globals.DEBUG_MARC) {
                    System.err.println("Ignoring rule " + rule + " because rhs is constructor");
                }
                continue;
            }
            final TRSSubstitution varSubst = e.getValue().x;
            final List<Pair<TRSVariable, TRSTerm>> argVarsAndTerms = e.getValue().y;

            programSB.append("if (randomChoice == ").append(Integer.toString(ruleNumber)).append(") then\n");

            for (final TRSTerm freshVar : varSubst.getCodomain()) {
                programSB.append(freshVar.toString()).append(" = random;\n");
            }
            programSB.append("if (");
            final TRSTerm cond = rule.getCondTerm();
            if (cond != null) {
                programSB.append(IDPExport
                    .exportTerm(cond.applySubstitution(varSubst), new PLAIN_Util(), IDPPredefinedMap.DEFAULT_MAP)
                    .replace("&&", "and")
                    .replace(" = ", " == "));
            } else {
                programSB.append("true");
            }
            programSB.append(") then\n");
            for (final Pair<TRSVariable, TRSTerm> argVarAndTerm : argVarsAndTerms) {
                programSB
                    .append(argVarAndTerm.x.toString())
                    .append(" = ")
                    .append(IDPExport.exportTerm(argVarAndTerm.y, new PLAIN_Util(), IDPPredefinedMap.DEFAULT_MAP))
                    .append(";\n");
            }
            programSB.append("() = ").append(calledSym.toString()).append("(");

            boolean isFirst = true;
            for (final Pair<TRSVariable, TRSTerm> argVarAndTerm : argVarsAndTerms) {
                if (!isFirst) {
                    programSB.append(", ");
                }
                isFirst = false;
                programSB.append(argVarAndTerm.x.toString());
            }
            programSB.append(");\nendif;\nendif;\n\n");
        }
        programSB.append("end\n");
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    public static class AddInterprocInvariantsProof extends Proof.DefaultProof {
        private final Map<FunctionSymbol, TRSFunctionApplication> fsToInvariantMap;

        public AddInterprocInvariantsProof(final Map<FunctionSymbol, TRSFunctionApplication> fsToInvariants) {
            this.setShortName("AddInterprocInvariantsProof");
            this.setLongName("AddInterprocInvariantsProof");
            this.fsToInvariantMap = fsToInvariants;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            result.append("Asked Interproc to generate invariants, got the following: ").append(o.linebreak());
            for (final Entry<FunctionSymbol, TRSFunctionApplication> e : this.fsToInvariantMap.entrySet()) {
                result
                    .append("For symbol ")
                    .append(e.getKey())
                    .append(" we got ")
                    .append(IDPExport.exportTerm(e.getValue(), o, IDPPredefinedMap.DEFAULT_MAP));
                result.append(o.newline());
            }
            return result.toString();
        }
    }
}
