package aprove.input.Programs.c;

import java.io.*;

import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.verification.oldframework.Input.*;

/**
 * Translator for C programs.
 * @author ffrohn
 * @version $Id$
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#getLanguage()
     */
    @Override
    public Language getLanguage() {
        return Language.C;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator.Skeleton#translate(aprove.verification.oldframework.Input.Input)
     */
    @Override
    public void translate(Input input) throws TranslationException {
        String queryStr = this.getProtoAnnotation();
        if (queryStr == null) {
            StringBuilder firstLine = new StringBuilder();
            try (InputStream inStream = input.getInputStream()) {
                char next;
                do {
                    next = (char)inStream.read();
                    firstLine.append(next);
                } while (next != '\n');
            } catch (IOException e) {
                throw new TranslationException(e);
            }
            // create a CharStream that reads from standard input
            // create a lexer that feeds off input CharStream
            queryStr = firstLine.toString();
        }
        LLVMQuery query;
        try {
            query = LLVMQuery.parseQuery(queryStr);
        } catch (LLVMParseException e) {
            throw new TranslationException(e);
        }
        this.setState(new CProblem(input.getPath(), query));
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#translate(java.io.Reader)
     */
    @Override
    public void translate(Reader reader) throws TranslationException {
        throw new UnsupportedOperationException();
    }

}
