package aprove.solver;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Utility.*;

public class MetaSolverFactory {

    private final static Properties props = MetaSolverFactory.loadProperties();
    private final static String[] orders = MetaSolverFactory.loadOrders();

    public static String[] getOrders() {
        return MetaSolverFactory.orders;
    }

    public static String getDisplayName(String name) {
        return MetaSolverFactory.props.getProperty(name+".DisplayName");
    }

    public static String getDefault(String key) {
        return MetaSolverFactory.props.getProperty(key);
    }

    private static String[] loadOrders() {
        return  MetaSolverFactory.props.getProperty("ORDERS").split(" ");
    }

    private static Properties loadProperties() {
        Properties props;

        Properties defaultprops = new Properties();
        try {
            PropertyLoader.fromResource(defaultprops, MetaSolverFactory.class, "solver.properties");
        } catch (IOException e) {
            System.err.println(e.getMessage());
            throw new RuntimeException("Where are my default props? D'oh!");
        }
        props = new Properties(defaultprops);
        try {
            PropertyLoader.fromFile(props, System.getProperty("user.home")+"/.aprove/solver.properties");
        } catch (IOException e) {}

        return props;
    }

}
