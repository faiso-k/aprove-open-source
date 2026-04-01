package aprove.strategies.Parameters;

import java.io.*;

/**
 * Created on 03.01.2005 by marmer
 *
 * @author: Martin Mertens
 * @version $Id$
 */

public class ModulePath {
    private static String PREDEFINED_ALIAS = "aprove.";
    public static final String PREDEFINED_PATH = "/aprove/predefinedstrategies/";

    public static InputStream moduleAsStream(String moduleName) {
        String filePath = moduleName.replace(ModulePath.PREDEFINED_ALIAS, ModulePath.PREDEFINED_PATH)
                                    .replace(".", "/");
        InputStream result = ModulePath.class.getResourceAsStream(filePath);
        if (result == null) {
            result = ModulePath.class.getResourceAsStream(filePath + ".strategy");
        }
        return result;
    }
}
