package aprove.verification.oldframework.CPF;

import java.io.*;

public interface CPF {
    /**
     * writes a CPF-file into an output-stream
     * @param ostream
     * @throws Exception
     */
    void writeCPF(OutputStream ostream) throws Exception;
}
