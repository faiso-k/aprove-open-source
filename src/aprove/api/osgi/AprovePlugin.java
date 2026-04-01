package aprove.api.osgi;

import java.net.*;
import java.util.*;

import org.osgi.framework.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * This is the Activator of the aprove.core Eclipse Plug-in.
 * 
 * This class should not be references from other classes,
 * because if Aprove is executed as a jar file and not as an Eclipse Plug-in,
 * loading this class will result in an Error. This is because this class references
 * classes from the OSGi Framework which are not available when Aprove is executed as a jar file.
 * 
 * However, it is fine to reference this class it is clear that Aprove is executed as an Eclipse Plug-in.
 * For example, the class {@link OsgiBundleClassProvider} uses this class to load resources.
 */
public class AprovePlugin implements BundleActivator {

    private static final String CLASS_RESOURCES_DIRECTORY = "/res-classes";

    public static AprovePlugin getDefault() {
        return plugin;
    }

    private static AprovePlugin plugin;

    private BundleContext context;

    @Override
    public void start(BundleContext context) throws Exception {
        enableAssertions();
        this.context = context;
        AprovePlugin.plugin = this;
        initGlobalState();
    }

    /**
     * This enables the assert keyword for the aprove.core plug-in. This is required,
     * since AProVE does only work correctly when assertions are activated. However,
     * we don't want to enable assertions for the complete Eclipse IDE that runs AProVE.
     * 
     * This works, since each OSGi bundle has its own class loader and the below statement
     * activates assertions only for the class loader of the current OSGi bundle,
     * which in this case is the aprove.core plug-in. Since the Activator is started before
     * any other class is loaded, assertions are enabled for all other classes.
     * 
     * WARNING: Ensure that in the MANIFEST.MF file this class is set as the bundle activator.
     * Also, ensure that the two check-boxes
     *     "Activate this plug-in when one of its classes is loaded" and
     *     "This plug-in is a singleton"
     * are checked.
     * 
     * See also http://stackoverflow.com/a/26277671/3888450
     */
    private void enableAssertions() {
        getClass().getClassLoader().setDefaultAssertionStatus(true);
    }

    private static void initGlobalState() {
        Main.UI_MODE = Main.UI.GUI;
        Main.firstObligation = true;
        Options.performEagerChecking = true;
    }

    @Override
    public void stop(BundleContext context) throws Exception {
        AprovePlugin.plugin = null;
    }

    public Iterator<URL> getResources(String path, String filePattern, boolean recurse) {
        Enumeration<URL> enumeration = context.getBundle().findEntries(path, filePattern, recurse);
        if (enumeration != null) {
            return enumerationAsIterator(enumeration);
        } else {
            return Collections.emptyIterator();
        }
    }

    private <T> Iterator<T> enumerationAsIterator(Enumeration<T> enumeration) {
        return new Iterator<T>() {

            @Override
            public T next() {
                return enumeration.nextElement();
            }

            @Override
            public boolean hasNext() {
                return enumeration.hasMoreElements();
            }
        };
    }

    public URL getResource(String path) {
        return context.getBundle().getEntry(path);
    }

    /**
     * The loading of resources for Eclipse Plug-ins is buggy.
     * It uses different mechanisms depending on whether or not the
     * Plug-in is executed from the Plug-in Development Environment (PDE)
     * or whether it is executed from the exported Plug-in. Thus, if it is executed from the PDE,
     * we add the "/res-classes" prefix to all resource requests.
     * 
     * To divide both cases, we check whether the "/res-classes" folder is accessible as a resource.
     * If it is, this plug-in is executed via the PDE.
     * 
     * http://www.eclipsezone.com/eclipse/forums/t101557.rhtml
     * https://bugs.eclipse.org/bugs/show_bug.cgi?id=153023
     * https://bugs.eclipse.org/bugs/show_bug.cgi?id=160133
     */
    public String getClassResourcePrefix() {
        if (getResource(CLASS_RESOURCES_DIRECTORY) != null) {
            // this plug-in is executed via the PDE
            return CLASS_RESOURCES_DIRECTORY;
        } else {
            // this plug-in is exported and then executed
            return "";
        }
    }
}
