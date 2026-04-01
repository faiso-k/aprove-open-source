package aprove.verification.oldframework.Utility;

import java.io.*;
import java.util.*;

/**
 * Property loading helper class.
 *
 * Ensures that no open files remain.
 */
public class PropertyLoader {

    /**
     * Loads properties from file
     */
    public static Properties fromFile(Properties p, String name) throws IOException {
        InputStream is = new FileInputStream(name);
        return PropertyLoader.fromInputStream(p, is);
    }

    /**
     * Loads properties from resource via class.getResourceAsStream
     */
    public static Properties fromResource(Properties p, Class clazz, String name) throws IOException {
        InputStream is = clazz.getResourceAsStream(name);
        return PropertyLoader.fromInputStream(p, is);
    }

    /**
     * Loads properties from InputStream and closes InputStream afterwards
     */
    public static Properties fromInputStream(Properties p, InputStream is) throws IOException {
        try {
            p.load(is);
        } finally {
            is.close();
        }
        return p;
    }

    /**
     * Loads properties from file
     */
    public static Properties fromXMLFile(Properties p, String name) throws IOException {
        InputStream is = new FileInputStream(name);
        return PropertyLoader.fromXMLInputStream(p, is);
    }

    /**
     * Loads properties from resource via class.getResourceAsStream
     */
    public static Properties fromXMLResource(Properties p, Class clazz, String name) throws IOException {
        InputStream is = clazz.getResourceAsStream(name);
        return PropertyLoader.fromXMLInputStream(p, is);
    }

    /**
     * Loads properties from InputStream and closes InputStream afterwards
     */
    public static Properties fromXMLInputStream(Properties p, InputStream is) throws IOException {
        try {
            p.loadFromXML(is);
        } finally {
            is.close();
        }
        return p;
    }
}
