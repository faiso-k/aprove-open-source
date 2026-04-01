package aprove.input.Utility.XML;

import org.xml.sax.*;

public interface TagHandler<Tags> {
    /**
     * Returns a tag handler for a tag occurring directly below the current tag.
     * @param tag
     * @return
     * @throws IllegalArgumentException If {@code tag} is no valid child tag.
     * @throws UnsupportedOperationException If there are no allowed child tags
     * at all.
     */
    public TagHandler<Tags> getSubHandler(Tags tag)
            throws IllegalArgumentException, UnsupportedOperationException;

    /**
     * @param cdata
     * accept {@code CDATA}.
     */
    public void appendCDATA(String cdata);

    /**
     * Called when the tag is closed.
     */
    public void finish();

    /**
     * Sets the attributes of the current tag.
     *
     * @param attributes
     */
    public void setAttributes(Attributes attributes);
}
