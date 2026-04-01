package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.prolog.structure.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;


class PrologToIRSwTEncoder {

    TRSTerm convertPrologTermToIRSwTTerm(PrologTerm term) {
        if(term.isVariable()) {
            return term.toTerm();
        }
        final TRSFunctionApplication prologApplication = (TRSFunctionApplication) term.toTerm();
        final FunctionSymbol irswtSymbol;
        switch(prologApplication.getRootSymbol().getName()) {
        case "=<": irswtSymbol = FunctionSymbol.create("<=", 2); break;
        case "=:=": irswtSymbol = FunctionSymbol.create("=", 2); break;
        case "=\\=": irswtSymbol = FunctionSymbol.create("=", 2); break;
        case "mod": irswtSymbol = FunctionSymbol.create("%", 2); break;
        case "//": irswtSymbol = FunctionSymbol.create("/", 2); break;
        default: irswtSymbol = prologApplication.getRootSymbol();
        }

        final ArrayList<TRSTerm> arguments = new ArrayList<>();
        for(PrologTerm argument : term.getArguments()) {
            arguments.add(this.convertPrologTermToIRSwTTerm(argument));
        }

        if(prologApplication.getRootSymbol().getName().equals("=\\=")) {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), TRSTerm.createFunctionApplication(irswtSymbol, arguments));
        } else {
            return TRSTerm.createFunctionApplication(irswtSymbol, arguments);
        }

    }

    /**
     * @param prologSubst Some substitution of variables by terms. Must not be null.
     * @return The same substitution in terms of IRSwT-Terms. Is not null.
     */
    Substitution convertPrologSubstitution(PrologSubstitution prologSubst) {
        assert prologSubst != null;

        final Map<TRSVariable, TRSTerm> backingCollection = new LinkedHashMap<>();
        for(Entry<PrologVariable, PrologTerm> substEntry : prologSubst.entrySet()) {
            backingCollection.put((TRSVariable) substEntry.getKey().toTerm(), this.convertPrologTermToIRSwTTerm(substEntry.getValue()));
        }
        return TRSSubstitution.create(ImmutableCreator.create(backingCollection));
    }

}