package aprove.verification.dpframework.IDPProblem.utility;

import java.io.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

/**
 * Hack to merge several ITRSs into one by renaming apart
 * user-defined symbols.
 *
 * @author fuhs
 */
public class ITRSMerger {

    public static void main(String[] args) {
        try {
            int lastInputIndex = args.length - 2;
            List<String> inFileNames = new ArrayList<String>();
            for (int i = 0; i <= lastInputIndex; ++i) {
                inFileNames.add(args[i]);
            }
            String outFile = args[lastInputIndex+1];
            ITRSMerger.mergeAndIO(inFileNames, outFile);
        }
        catch (Exception e) {
            System.err.println("Usage: java -jar itrsmerger.jar infile_1 infile_2 .. infile_n outfile");
            System.err.println("Here n may be 0, then an empty ITRS will be generated.");
            System.err.println("If infile_i is the empty string, it is ignored");
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }


    /**
     *
     * @param inFileNames - ITRSs to unite disjointly
     * @param outFile - the disjoint union of the ITRSs in
     *  <code>inFileNames</code> will be stored here
     */
    public static void mergeAndIO(List<String> inFileNames, String outFile) {
        ArrayList<ITRSProblem> inITRSs = ITRSMerger.readFiles(inFileNames);
        ITRSProblem result = ITRSMerger.merge(inITRSs);
        String outString = result.toExternString();
        try {
            Writer itrsWriter = new OutputStreamWriter(new FileOutputStream(outFile));
            itrsWriter.write(outString);
            itrsWriter.flush();
            itrsWriter.close();
        }
        catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }


    private static ArrayList<ITRSProblem> readFiles(Collection<String> inFileNames) {
        ArrayList<ITRSProblem> result = new ArrayList<ITRSProblem>(inFileNames.size());
        for (String name : inFileNames) {
            if (name.length() > 0) {
                ITRSProblem itrs = ITRSMerger.loadITRS(name);
                result.add(itrs);
            }
        }
        return result;
    }

    /**
     * @param inITRSs - arbitrary number of ITRSs
     * @return an ITRS that is the disjoint union of <code>inITRSs</code>,
     *  the empty ITRS in case of the empty list
     */
    public static ITRSProblem merge(ArrayList<ITRSProblem> inITRSs) {
        switch (inITRSs.size()) {
        case 0   : return ITRSProblem.create(java.util.Collections.<GeneralizedRule>emptyList(),
                                   new IQTermSet(new QTermSet(java.util.Collections.<TRSFunctionApplication>emptyList()),
                                   IDPPredefinedMap.DEFAULT_MAP));
        case 1   : return inITRSs.get(0); // nothing to change :)
        default : return ITRSMerger.mergeSeveral(inITRSs);
        }
    }

    /**
     *
     * @param inITRSs - at least two ITRSProblems
     * @return the merged ITRS, its defined symbols renamed apart
     */
    private static ITRSProblem mergeSeveral(ArrayList<ITRSProblem> inITRSs) {
        int size = inITRSs.size();

        // * gather names of all occurring function symbols and variables
        //   (cannot be used for fresh names)
        Set<String> usedNames = new LinkedHashSet<String>();
        for (ITRSProblem itrs : inITRSs) {
            ITRSMerger.collectNames(itrs, usedNames);
        }
        // * gather name replacement maps for names for each ITRSProblem:
        //   per ITRSProblem I, we shall replace each user-defined
        //   symbol f by a new fresh name f_I
        List<Map<FunctionSymbol, FunctionSymbol>> symbolRenamings = new ArrayList<Map<FunctionSymbol, FunctionSymbol>>(size);
        FreshNameGenerator fridge; // inspired by cryingshadow
        NameGenerator ng = new AppendNameGenerator(0, 0);
        fridge = new FreshNameGenerator(usedNames, ng);

        for (ITRSProblem itrs : inITRSs) {
            IDPPredefinedMap predefMap = itrs.getPredefinedMap();
            Map<FunctionSymbol, FunctionSymbol> renaming = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
            ImmutableSet<FunctionSymbol> inSyms = itrs.getRuleAnalysis().getFunctionSymbols();
            for (FunctionSymbol usedSym : inSyms) {
                // the next line is a bit nasty (what with predefined domains varying)
                if (! predefMap.isPredefined(usedSym) && ! IDPPredefinedMap.DEFAULT_MAP.isPredefined(usedSym)) {
                    // by all means user-defined, so we need a replacement
                    String usedName = usedSym.getName();
                    int arity = usedSym.getArity();
                    FunctionSymbol freshSym;
                    do {
                        // no accidental generation of pre-defined symbols
                        // wrt the IDPPredefinedMap that shall be used in
                        // the new ITRSProblem
                        String freshName = fridge.getFreshName(usedName, false);
                        freshSym = FunctionSymbol.create(freshName, arity);
                    } while (IDPPredefinedMap.DEFAULT_MAP.isPredefined(freshSym));
                    renaming.put(usedSym, freshSym);
                }
            }
            symbolRenamings.add(renaming);
        }

        // * now gather rules and apply symbol renamings
        Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        for (int i = 0; i < size; ++i) {
            ITRSProblem itrs = inITRSs.get(i);
            Map<FunctionSymbol, FunctionSymbol> renaming = symbolRenamings.get(i);
            for (GeneralizedRule oldRule : itrs.getR()) {
                TRSFunctionApplication newLeft = (TRSFunctionApplication) ITRSMerger.rename(oldRule.getLeft(), renaming);
                TRSTerm newRight = ITRSMerger.rename(oldRule.getRight(), renaming);
                GeneralizedRule newRule = GeneralizedRule.create(newLeft, newRight);
                newRules.add(newRule);
            }
        }

        RuleAnalysis<GeneralizedRule> rAnalysis = new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(newRules), IDPPredefinedMap.DEFAULT_MAP);
        ITRSProblem result = ITRSProblem.create(rAnalysis,
                                new IQTermSet(new QTermSet(rAnalysis.getLeftHandSides()),
                                                IDPPredefinedMap.DEFAULT_MAP));
        return result;
    }

    /**
     * @param itrs
     * @param usedNames - all names of used-defined function symbols
     *  and variables shall be added here
     */
    private static void collectNames(ITRSProblem itrs, Set<String> usedNames) {
        RuleAnalysis<GeneralizedRule> ruleAnalysis = itrs.getRuleAnalysis();
        for (HasName hn : ruleAnalysis.getFunctionSymbols()) {
            usedNames.add(hn.getName());
        }
        for (HasName hn : ruleAnalysis.getVariables()) {
            usedNames.add(hn.getName());
        }
    }

    /**
     * @param t
     * @param renaming
     * @return a term t' which is like t, but with all function symbols f
     *  replaced by g if renaming(f) = g (a function symbol h is not
     *  replaced if renaming(h) = null or if h is pre-defined)
     */
    private static TRSTerm rename(TRSTerm t, Map<FunctionSymbol, FunctionSymbol> renaming) {
        if (t.isVariable()) {
            return t;
        }
        TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        FunctionSymbol oldRoot = fApp.getRootSymbol();
        FunctionSymbol newRoot = renaming.get(oldRoot);
        if (newRoot == null) {
            newRoot = oldRoot;
        }
        List<TRSTerm> oldArgs = fApp.getArguments();
        int size = oldArgs.size();
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(size);
        for (int i = 0; i < size; ++i) {
            TRSTerm newArg = ITRSMerger.rename(oldArgs.get(i), renaming);
            newArgs.add(newArg);
        }
        TRSTerm res = TRSTerm.createFunctionApplication(newRoot, newArgs);
        return res;
    }

    /**
     * Loads an ITRSProblem from a file.
     */
    private static ITRSProblem loadITRS(String srcfile) {
        aprove.input.Programs.itrs.Translator trans = new aprove.input.Programs.itrs.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        ITRSProblem result = (ITRSProblem) trans.getState();
        return result;
    }

}
