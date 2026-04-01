/*
 * Created on Feb 7, 2005
 */
package aprove.verification.oldframework.Utility.GenericStructures;

/**
 * @author rabe
 */
public class Quadruple<W,X,Y,Z> {

    public W w;
    public X x;
    public Y y;
    public Z z;

    public Quadruple(){
    }

    public Quadruple(W w, X x, Y y, Z z) {
        this.w = w;
        this.x = x;
        this.y = y;
        this.z = z;
    }

    @Override
    public boolean equals(Object object) {

        if(object instanceof Quadruple) {
            Quadruple that =(Quadruple)object;
            return this.w.equals(that.w) && this.x.equals(that.x) && this.y.equals(that.y) && this.z.equals(that.z);
        }else{
            return false;
        }

    }

    @Override
    public String toString() {
        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append("(");
        stringBuffer.append(this.w+",");
        stringBuffer.append(this.x+",");
        stringBuffer.append(this.y+",");
        stringBuffer.append(this.z+")");
        return stringBuffer.toString();
    }

    @Override
    public int hashCode() {
        int hashW = this.w != null ? this.w.hashCode() : 0;
        int hashX = this.x != null ? this.x.hashCode() : 0;
        int hashY = this.y != null ? this.y.hashCode() : 0;
        int hashZ = this.z != null ? this.z.hashCode() : 0;
        return hashW + 101 * hashX + 202 * hashY + 303 * hashZ;
    }

}
