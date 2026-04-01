package aprove.verification.idpframework.Processors.Filters;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class LongNamesFilter extends AbstractIDPFilter<Result, IDPProblem> {

    public static class Arguments {
        public int nameLengthThreshold = 10;
        public int newNameLength = 5;
    }

    private final int nameLengthThreshold;
    private final int newNameLength;

    @ParamsViaArgumentObject
    public LongNamesFilter(final Arguments arguments) {
        super("LongNamesFilter", FilterMode.QUANTIFY_FILTERED_VARIABLES);
        this.nameLengthThreshold = arguments.nameLengthThreshold;
        this.newNameLength = arguments.newNameLength;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem idp,
        final Abortion aborter) throws AbortionException {
        final FilterReplacement filter =
            this.createFilter(idp, aborter);

        final IDPProblem newIDP =
            this.createNewIDP(idp, filter, aborter);

        if (newIDP != idp) {
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT,
                new LongNamesFilterProof(filter));
        }
        return ResultFactory.unsuccessful();
    }

    private FilterReplacement createFilter(final IDPProblem idp,
        final Abortion aborter) {
        final FunctionSymbolReplacement fsReplacement = new FunctionSymbolReplacement();

        final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.FRIENDLYNAMES);
        freshNames.lockHasNames(idp.getIdpGraph().getFunctionSymbols());
        final IDPPredefinedMap predefinedMap = idp.getPredefinedMap();

        for (final IFunctionSymbol<?> fs : idp.getIdpGraph().getFunctionSymbols()) {
            if (fs.getSemantics() == null && fs.getName().length() > this.nameLengthThreshold) {
                final String name = fs.getName();
                final String[] nameSplit = name.split("[,._]");
                String shortName;
                if (nameSplit.length > 1) {
                    final StringBuilder shortNameBuilder = new StringBuilder();
                    for (int i = 0; i < nameSplit.length && i < this.newNameLength; i++) {
                        final String curSplitPart = nameSplit[i];
                        //Ignore empty parts:
                        if (curSplitPart.length() == 0) {
                            continue;
                        }
                        try {
                            Integer.parseInt(curSplitPart);
                            shortNameBuilder.append(curSplitPart + "_");
                        } catch (final NumberFormatException e) {
                            if (nameSplit[i].length() > 0) {
                                shortNameBuilder.append(nameSplit[i].charAt(0));
                            }
                        }
                    }
                    shortName = shortNameBuilder.toString();
                } else if (name.matches("([a-z]+[A-Z0-9]+)*[a-z]*")) {
                    shortName = name.charAt(0) + name.replaceAll("[a-z]+", "");
                } else {
                    shortName = name.substring(0, this.newNameLength);
                }

                shortName = freshNames.getFreshName(shortName, false);
                final IFunctionSymbol<?> newFs = IFunctionSymbol.changeName(fs, predefinedMap, shortName);
                fsReplacement.put(fs,
                    new ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>(
                            newFs,
                            FunctionSymbolReplacement.createRetainAllPositions(fs)));
            }
        }

        return new FilterReplacement(fsReplacement, VarRenaming.EMPTY_RENAMING);
    }

    public static class LongNamesFilterProof extends AbstractFilterProof {

        public LongNamesFilterProof(final FilterReplacement filter) {
            super(filter);
        }

    }
}