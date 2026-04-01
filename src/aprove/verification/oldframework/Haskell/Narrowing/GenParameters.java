package aprove.verification.oldframework.Haskell.Narrowing;

public class GenParameters{
    public int maxArgumentHeadVariants = 200;
    public int monoNestingDepth = 6;
    public int multiNestingDepth = 3;

    public GenParameters(int maxArgumentHeadVariants,int monoNestingDepth,int multiNestingDepth){
        this.maxArgumentHeadVariants = maxArgumentHeadVariants;
        this.monoNestingDepth = monoNestingDepth;
        this.multiNestingDepth = multiNestingDepth;
    }

    public GenParameters(){

    }

}

