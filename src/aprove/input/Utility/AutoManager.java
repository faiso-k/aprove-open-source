package aprove.input.Utility;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.input.*;
import aprove.strategies.Parameters.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Created on 07.06.2005 by marmer Small factory that delivers auto strategies
 * from the package aprove.predefinedstrategies.Auto. It uses the property file
 * automatic_strategies.properties.
 * @author marmer
 * @version $Id$
 */

public class AutoManager {

    private static Properties PROPERTIES_Termination = AutoManager.generateProperties("automatic_strategies.properties");
    private static Properties PROPERTIES_RC = AutoManager.generateProperties("automatic_strategies_rc.properties");
    private static Properties PROPERTIES_TheoremProver =
        AutoManager.generateProperties("automatic_strategies_theoremprover.properties");

    private static Properties generateProperties(final String propertyFileName) {
        final Properties properties = new Properties();
        try {
            PropertyLoader.fromResource(properties, AutoManager.class, propertyFileName);
        } catch (final IOException e) {
            e.printStackTrace();
        }
        return properties;
    }

    public static StrategyProgram getStrategyProgramForTypedInput(final TypedInput type) {
        String value = null;
        final HandlingMode hm = type.getModedType().getHandlingMode();

        if (hm.equals(HandlingMode.Termination)) {
            value = AutoManager.PROPERTIES_Termination.getProperty(type.getLanguage().toString());
        } else if (hm.equals(HandlingMode.TheoremProver)) {
            value = AutoManager.PROPERTIES_TheoremProver.getProperty(type.getLanguage().toString());
        } else if (hm.equals(HandlingMode.RuntimeComplexity)) {
            value = AutoManager.PROPERTIES_RC.getProperty(type.getLanguage().toString());
        }

        if (value == null) {
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("Warning: No auto strategy defined for typed input of type " + type + ".");
                System.err.println("At the moment, the following entries are stored in automatic_strategies.properties:");
                System.err.println("Please add the auto strategy for " + type);
            }
            return null;
        }
        return EasyInput.loadStrategyModule(value);
    }
}
