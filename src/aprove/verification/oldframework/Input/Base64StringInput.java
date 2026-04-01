package aprove.verification.oldframework.Input;

import java.io.*;

/**
 * Like a StringInput, but the stored string is a base64 representation of the actual data. For UTF-8 data this is not
 * a problem (we just need to decode). For binary data we provide the actual bytes instead (so that we do not have any
 * charset related problems).
 * @author cotto
 */
public class Base64StringInput extends StringInput {

    public Base64StringInput(final String content, final String name, final String extName) {
        super(content, name, extName);
    }

    /**
     * @return the represented decoded string. Note that this is a bad idea for binary data.
     */
    @Override
    public String getString() {
        final byte[] decodedArray = this.decode();
        final String string = new String(decodedArray);
        return string;
    }

    /**
     * @return the decoded bytes
     */
    private byte[] decode() {
        return org.apache.commons.codec.binary.Base64.decodeBase64(super.getString());
    }

    /**
     * @return a buffered stream giving access to the represented (decoded) bytes
     */
    @Override
    public BufferedInputStream getInputStream() {
        final byte[] array = this.decode();
        final InputStream is = new ByteArrayInputStream(array);
        return new BufferedInputStream(is);
    }
}
