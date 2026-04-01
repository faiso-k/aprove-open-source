package aprove.verification.oldframework.ExternalProcess;

import java.io.*;

public interface Checker<T> {
    T readResult(BufferedReader result) throws IOException;
}