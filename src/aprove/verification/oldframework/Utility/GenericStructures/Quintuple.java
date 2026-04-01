package aprove.verification.oldframework.Utility.GenericStructures;


public class Quintuple<V,W,X,Y,Z> {

    public V v;
    public W w;
    public X x;
    public Y y;
    public Z z;

    public Quintuple(){
    }

    public Quintuple(V v, W w, X x, Y y, Z z) {
        this.v = v;
        this.w = w;
        this.x = x;
        this.y = y;
        this.z = z;
    }

    @Override
    public boolean equals(Object object) {

        if(object instanceof Quintuple) {
            Quintuple that =(Quintuple)object;
            return this.v.equals(that.v) && this.w.equals(that.w) && this.x.equals(that.x) && this.y.equals(that.y) && this.z.equals(that.z);
        }else{
            return false;
        }

    }

    @Override
    public String toString() {
        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append("(");
        stringBuffer.append(this.v+",");
        stringBuffer.append(this.w+",");
        stringBuffer.append(this.x+",");
        stringBuffer.append(this.y+",");
        stringBuffer.append(this.z+")");
        return stringBuffer.toString();
    }

    @Override
    public int hashCode() {
        int hashv = this.v != null ? this.v.hashCode() : 0;
        int hashW = this.w != null ? this.w.hashCode() : 0;
        int hashX = this.x != null ? this.x.hashCode() : 0;
        int hashY = this.y != null ? this.y.hashCode() : 0;
        int hashZ = this.z != null ? this.z.hashCode() : 0;
        return 17 * hashv + 28 * hashW + 103 * hashX + 202 * hashY + 299 * hashZ;
    }

}
