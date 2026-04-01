package aprove.strategies.Parameters;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Utility.*;

public class Util {

    public static Properties loadPropertyFile(String filename) throws IOException{
        return PropertyLoader.fromResource(new Properties(), ParameterManager.class, "Properties/" + filename);
    }

}
