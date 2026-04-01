/*
 * Created on 31.03.2004
 *
 */
package aprove.prooftree.Export.Utility;

/**
 * @author nowonder
 *
 * PLAIN_Able is only used by PLAIN_Util. If implemented, toPLAIN() is used
 * instead of the generic {@link Export_Util#export(Object)} method. So
 * PLAIN_Able SHOULD NOT be implemented, unless the intended plain text export
 * differs from the <code>export()</code> output.
 */
@Deprecated
public interface PLAIN_Able {
    String toPLAIN();
}
