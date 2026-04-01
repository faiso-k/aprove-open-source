package aprove.verification.oldframework.Input.Annotators;

import java.io.*;
import java.util.*;

import aprove.runtime.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.theoremprover.TheoremProver.*;

public class TheoremProverAnnotator implements Annotator{
    @Override
    public Annotation annotate(TypedInput typedInput){
        if(!typedInput.getHandlingMode().equals(HandlingMode.TheoremProver)
                || !typedInput.getLanguage().equals(Language.FP)) {
            throw new RuntimeException("no theorem prover for FP");
        }

        ProgramContainingFormulas fpp = (ProgramContainingFormulas)typedInput.getInput();
        List<Formula> formulas = fpp.getFormulas();
        Program program = fpp.getProgram();

        LemmaDatabase ldb = LemmaDatabaseFactory.getLemmmaDatabase();
        ldb.programUpdated(program, true);
        String lemmaDataBaseFileName = Options.lemmaDatabaseFileName;
        if (lemmaDataBaseFileName != null && !lemmaDataBaseFileName.equals("")){
            ldb.importTXTDatabase(new File(lemmaDataBaseFileName), true);
        }

        return new FormulaAnnotation(formulas,program);
    }
}
