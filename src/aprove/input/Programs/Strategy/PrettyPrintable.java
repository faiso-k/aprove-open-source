package aprove.input.Programs.Strategy;

import java.io.*;

public interface PrettyPrintable {
    public int getOneLineSize(int precedence);

    public void print(Appendable ap, PrettyPrintState pps) throws IOException;
}
