package aprove.input.Programs.llvm;

import java.io.*;

import org.antlr.runtime.*;

import aprove.input.Generated.llvm.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Janine Repke, CryingShadow
 * Translator for LLVM source files.
 */
public class Translator extends ProgramTranslator {

    /**
     * The parse result.
     */
    private LLVMProblem llvmProblem;

    /**
     * The query which can be set by the constructor, parsed from the
     * proto-annotation or parsed from the first line of the input file.
     */
    private LLVMQuery query;

    /**
     * Default constructor.
     */
    public Translator() {
        // empty
    }

    /**
     * @param query
     */
    public Translator(LLVMQuery query) {
        this.query = query;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#getLanguage()
     */
    @Override
    public Language getLanguage() {
        return Language.LLVM;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.ProgramTranslator#getState()
     */
    @Override
    public LLVMProblem getState() {
        return this.llvmProblem;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator.Skeleton#translate(java.io.InputStream)
     */
    @Override
    public void translate(InputStream inStream) throws TranslationException {
        try {
            if (this.query == null) {
                // query has not yet been set, parse it from the
                // proto-annotation or the first line of the input file
                String queryStr = this.getProtoAnnotation();
                if (queryStr == null) {
                    StringBuilder firstLine = new StringBuilder();
                    char next;
                    do {
                        next = (char) inStream.read();
                        firstLine.append(next);
                    } while (next != '\n');
                    // create a CharStream that reads from standard input
                    // create a lexer that feeds off input CharStream
                    queryStr = firstLine.toString();
                }
                this.query = LLVMQuery.parseQuery(queryStr);
            }
            this.translate(new LLVMLexer(new ANTLRInputStream(inStream)));
        } catch (IOException ioException) {
            throw new TranslationException("Cannot read from llvm input stream.\n" + ioException.getMessage());
        } catch (LLVMParseException e) {
            throw new TranslationException("Cannot parse llvm input.\n" + e.getMessage());
        }
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#translate(java.io.Reader)
     */
    @Override
    public void translate(Reader reader) throws TranslationException {
        try {
            StringBuilder firstLine = new StringBuilder();
            if (this.query == null) {
                // query has not yet been set, parse it from the
                // proto-annotation or the first line of the input file
                String queryStr = this.getProtoAnnotation();
                if (queryStr == null) {
                    char next;
                    do {
                        next = (char)reader.read();
                        firstLine.append(next);
                    } while (next != '\n');
                    queryStr = firstLine.toString();
                }
                this.query = LLVMQuery.parseQuery(queryStr);
            }
            // create a CharStream that reads from standard input
            // create a lexer that feeds off input CharStream
            try (SequenceReader sequence = new SequenceReader(new StringReader(firstLine.toString()), reader)) {
                this.translate(new LLVMLexer(new ANTLRReaderStream(sequence)));
            }
        } catch (IOException ioException) {
            throw new TranslationException("Cannot read from llvm input stream.\n" + ioException.getMessage());
        } catch (LLVMParseException e) {
            throw new TranslationException("Cannot parse llvm input.\n" + e.getMessage());
        }
    }

    /**
     * @param lexer The lexer.
     * @throws TranslationException If parsing is not successful.
     */
    private void translate(LLVMLexer lexer) throws TranslationException {
        try {
            // create a buffer of tokens pulled from the lexer
            // create a parser that feeds off the token buffer
            // begin parsing
            // make transformation to a working structure
            this.llvmProblem =
                LLVMProblem.create(
                    new LLVMParser(new CommonTokenStream(lexer)).module().createBasicStructure(),
                    this.query,
                    false
                );
        } catch (RecognitionException recException) {
            throw new TranslationException("Cannot parse llvm file." + recException.getMessage());
        } catch (LLVMParseException llvmParseException) {
            throw new TranslationException(
                "Cannot create the llvm module from the llvm parse module.\n"
                + llvmParseException.getMessage()
            );
        }
    }

}
