package aprove.input.Programs.llvm.problems;

import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;

import java.io.File;
import java.util.logging.Logger;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

/**
 * Problem instance of an LLVM program and a starting query.
 * @author Janine Repke, CryingShadow, ffrohn
 */
public abstract class LLVMProblem extends DefaultBasicObligation {

    /**
     * Logger.
     */
    public static final Logger logger = Logger.getLogger("aprove.input.Programs.llvm.problems.LLVMProblem");

    /**
     * @param basicModuleParam The LLVM program.
     * @param queryParam The starting query.
     * @param fromC Is the LLVM program used to actually analyze a C program?
     * @return An LLVMProblem with the specified program and query. The live variables are computed from the program.
     */
    public static LLVMProblem create(LLVMModule basicModuleParam, LLVMQuery queryParam, boolean fromC) {
        return LLVMProblem.create(basicModuleParam, queryParam, fromC, null);
    }

    /**
     * @param basicModuleParam The LLVM program.
     * @param queryParam The starting query.
     * @param fromC Is the LLVM program used to actually analyze a C program?
     * @param fileToRemove {@link LLVMProblem#fileToRemove}
     * @return An LLVMProblem with the specified program and query.
     */
    public static LLVMProblem create(
        LLVMModule basicModuleParam,
        LLVMQuery queryParam,
        boolean fromC,
        File fileToRemove
    ) {
        switch (queryParam.getHandlingMode()) {
            case Termination:
                return
                    new LLVMTerminationProblem(
                        basicModuleParam,
                        queryParam,
                        fromC,
                        fileToRemove
                    );
            case MemorySafety:
                return new LLVMMemSafetyProblem(basicModuleParam, queryParam, fromC, fileToRemove);
            case RuntimeComplexity:
                return new LLVMComplexityProblem(basicModuleParam, queryParam, fromC, fileToRemove);
            default:
                throw new IllegalArgumentException();
        }
    }

    /**
     * The LLVM program.
     */
    private final LLVMModule basicModule;

    /**
     * Flag indicating whether this LLVM program is used to actually analyze a C program.
     */
    private final boolean compiledC;

    /**
     * The source file that should be removed after the graph construction.
     * If it is null, then nothing should be removed.
     */
    private final File fileToRemove;

    /**
     * The starting query.
     */
    private final LLVMQuery query;

    /**
     * @param basicModuleParam The LLVM program.
     * @param queryParam The starting query.
     * @param fromC Is the LLVM program used to actually analyze a C program?
     * @param fileToRemove {@link LLVMProblem#fileToRemove}
     */
    protected LLVMProblem(LLVMModule basicModuleParam, LLVMQuery queryParam, boolean fromC, File fileToRemove) {
        super("LLVM problem", "LLVM IR problem");
        this.basicModule = basicModuleParam;
        this.query = queryParam;
        this.fileToRemove = fileToRemove;
        this.compiledC = fromC;
    }

    /**
     * removes {@link LLVMProblem#fileToRemove}, if necessary.
     */
    public void cleanUp() {
        if (this.fileToRemove != null) {
            this.fileToRemove.delete();
        }
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        res.append("LLVM Problem");
        res.append(o.linebreak());
        res.append(o.linebreak());
        res.append(this.basicModule.export(o));
        res.append(o.linebreak());
        res.append(o.linebreak());
        res.append(this.query.export(o));
        return res.toString();
    }

    /**
     * @return The LLVM program.
     */
    public LLVMModule getBasicModule() {
        return this.basicModule;
    }

    /**
     * @return {@link LLVMProblem#fileToRemove}
     */
    public File getFileToRemove() {
        return this.fileToRemove;
    }

    /**
     * @return The starting query.
     */
    public LLVMQuery getQuery() {
        return this.query;
    }

    /**
     * @param fileToRemove {@link LLVMProblem#fileToRemove}
     * @return TODO
     */
    public abstract LLVMProblem setFileToRemove(File fileToRemove);

    /**
     * @return This LLVM problem marked such that it is used to actually analyze a C program.
     */
    public abstract LLVMProblem setFromC();

    /**
     * @return True if this LLVM program is used to actually analyze a C program. False otherwise.
     */
    public boolean wasC() {
        return this.compiledC;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        return CPFTag.LLVM_PROG.create(doc, "\n" + this.basicModule.toLLVMIR());
    }

}
