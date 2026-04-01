package aprove.verification.oldframework.Algebra.Matrices.Interpretation;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * TermInterpretors interpret terms into matrices.
 * They can either be generic (before search) or specialized (after a solution has been found).
 * @author kabasci
 * @version $Id$
 */
public class TermInterpretor {




  // Counter for generating fresh names for temp variables.
  protected static long counter = 0;
  protected static synchronized long getFreshNum() {
      return TermInterpretor.counter++;
  }



  // Symbol representations for the Matrix order - generic before search, specialized afterwards
  protected final SymbolRepresentations repres;

  // The argument interpretor, specifically important if we use anything nonlinear.
  protected final ArgumentInterpretor argInt;

  // The Matrix factory, specifying shape, dimension and possible search space restrictions
  protected final MatrixFactory fact;

  // Only applicable in certain situations (i.e. non-rational matrices): Stores already interpreted terms for future use if they again occur as subterms
  protected Map<TRSTerm, Matrix> cache = new HashMap<TRSTerm, Matrix>();

  // The specialization map.
  protected Map<String, BigInteger> result = null;

  // Do we use rational coefficients? (Special logic needed, i.e. caching is not permitted etc.)
  protected boolean rational = false;

  /**
   * Used to specify different ranges for coefficients, specifically temporary coefficients.
   * fuhs: Converted from IntegerInterval to BigIntegerInterval.
   * It seems that the lower bound of the interval is always 0,
   * which does not need to be represented explicitly. (Right?) [Yes]
   *
   */
  protected Map<String, BigIntegerInterval> ranges;

  // If we use a nonstandard ordering, this map can be used to transform terms into original terms
  // for instance for case differentiations in max-min usages.
  protected Map<TRSTerm, TRSTerm> transformationMap = new HashMap<TRSTerm, TRSTerm>();

  // Gathered extra constraints to pass on to the solver, f.i. flattening cache constraints
  protected final Set<MatrixConstraint> extraConstraints = new LinkedHashSet<MatrixConstraint>();

  // Debug field: set to false to disable term flattening (makes nonlinear MATRO unbearably slow, but flattening currently seems buggy)
  protected boolean flatten = true;


  protected static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Matrices.Interpretation.TermInterpretor");

  /**
   * Creates a TermInterpretator creating the representation matrices.
   * @param dpSignature
   * @param signature
   * @param fact
   */
  public TermInterpretor(final ImmutableSet<FunctionSymbol> dpSignature,
            final ImmutableSet<FunctionSymbol> signature,
            final ImmutableSet<TRSVariable> variables, final MatrixFactory fact,
            final ArgumentInterpretor argInt, final BigInteger range,
            final boolean rational, final int denominator) {
      this.ranges = new DefaultValueMap<String, BigIntegerInterval>(
              new BigIntegerInterval(BigInteger.ZERO, range));

      this.repres = new SymbolRepresentations(fact);
      this.repres.denominator = denominator;
      this.fact = fact;
      this.argInt = argInt;

      // Rational matrices hack
      this.rational = rational;
      argInt.setTermInterpretor(this);

      // Generate DP Representators
      for (final FunctionSymbol F: dpSignature) {
          final String name = F.getName() + "[" + F.getArity() + "]";
          this.repres.dpSyms.put(F, fact.createDPFSymCoefficientMatrix(name + "_"));
          this.repres.multifArgSyms.put(F, new HashMap<String, Matrix>());
          final Map<Integer, Matrix> args = new LinkedHashMap<Integer, Matrix>();

          for (int i=0; i < F.getArity(); i++) {
              args.put(i, fact.createDPArgSymCoefficientMatrix(name + "{" + (i+1) + "}_"));
          }
          this.repres.functionArgSyms.put(F, args);

      }
      // Generate FSymbol Representators
      for (final FunctionSymbol f: signature) {
          final String name = f.getName() + "[" + f.getArity() + "]";
          this.repres.functionSyms.put(f, fact.createFSymCoefficientMatrix(name + "_"));
          this.repres.multifArgSyms.put(f, new HashMap<String, Matrix>());
          final Map<Integer, Matrix> args = new LinkedHashMap<Integer, Matrix>();

          for (int i=0; i < f.getArity(); i++) {
              args.put(i, fact.createArgSymCoefficientMatrix(name + "{" + (i+1) + "}_"));
          }
          this.repres.functionArgSyms.put(f, args);
      }
      // Generate Variable Representators
      for (final TRSVariable x: variables) {
          if (!x.getName().startsWith("(")) {
              // These will be generated seperately.
              this.repres.getVarSyms().put(x, fact.createVariableMatrix(x.getName()));
          }
          // Also hard-generate an instance of x.
          this.repres.getVarSyms().put(TRSTerm.createVariable("x"), fact.createVariableMatrix("x"));


      }


  }


  /**
   * Creates a TermInterpretator if the symbols have allready been created.
   * @param fact
   * @param repres
   * @param cache
   *
   */
  public TermInterpretor(final MatrixFactory fact, final SymbolRepresentations repres, final ArgumentInterpretor argInt, final Map<TRSTerm, Matrix> cache, final boolean rational) {
      this.repres = repres;
      this.argInt = argInt;
      argInt.setTermInterpretor(this);
      this.fact = fact;
      this.cache = cache;
      this.rational = rational;
  }

  /**
   * Copying a TermInterpretor
   * @param repres The specialized Representations
   * @param ti The old TermInterpretor
   * @param result
   */
  public TermInterpretor(final TermInterpretor ti, final Map<String, BigInteger> result) {
      this.repres = ti.repres;
      this.argInt = ti.argInt;
      this.rational = ti.rational;
      this.result = result;
      this.argInt.setTermInterpretor(this);
      this.fact = ti.fact;
      this.transformationMap = ti.transformationMap;
      this.cache = ti.cache;
  }

  /**
   * Specialize a TermInterpretor, discarding its cache
   * @param repres The specialized Representations
   * @param ti The old TermInterpretor
   * @param result
   */
  public TermInterpretor(final SymbolRepresentations repres, final TermInterpretor ti, final Map<String, BigInteger> result) {
      this.repres = repres;
      this.argInt = ti.argInt;
      this.result = result;
      this.rational = ti.rational;
      this.argInt.setTermInterpretor(this);
      this.fact = ti.fact;
      this.transformationMap = ti.transformationMap;
      this.cache = new LinkedHashMap<TRSTerm, Matrix>();
  }



  /**
   * Shortcut to interpret terms in nonrational case.
   * @param t The term to interpret
   * @return
   */
  public Matrix interpretTerm(final TRSTerm t) {
      return this.interpretTerm(t, 1, null, t, 0);
  }

  /**
   * Interprets a Term into a Matrix. This method can be used to interpret terms in any matrix setting, including rational.
   * @param t The Term to interpret.
   * @param varColumns The amount of columns per variable matrix
   * @param mappedVars The prior map of Variables to Matrices if we use special orders and have bound variables (f.i. (>=x) in max-min)
   * @param root The root of the subterm being interpreted; used for rational.
   * @param depth The depth of the position of the term t in the root term
   * @return
   */
  public Matrix interpretTerm(TRSTerm t, final int varColumns, final Map<TRSVariable, Matrix> mappedVars, final TRSTerm root, final int depth) {

      if (this.result != null) {
          // We are specialized. First, apply neccesary transformations to term.
          while (this.transformationMap.containsKey(t)) {
              t = this.transformationMap.get(t);
          }
      }
      // If not rational: use cache. Since in rational mode interpretations depend on depth, we cannot use the cache so far.
      Matrix m;
      if (!this.rational) {
          m = this.cache.get(t);
          if (m!= null) {
              if (this.result != null ) {
                  m = m.specialize(this.result);
              }
              return m;
          }
      }



      if (t instanceof TRSFunctionApplication) {

          final TRSFunctionApplication f = (TRSFunctionApplication)t;
          List<Matrix> argInterpret = new ArrayList<Matrix> (f.getArguments().size());

          if (!this.repres.dpSyms.containsKey(f.getRootSymbol())) {
              final Matrix[] interpretations = new Matrix[f.getArguments().size()];
              for (int i=0; i<f.getArguments().size(); i++) {
                  final Matrix inter = this.interpretTerm(f.getArgument(i), 1, null, root, depth + 1);

                  if(this.result != null) {
                      if (!this.flatten || this.rational ) {
                          interpretations[i] = inter;
                      } else {
                          interpretations[i] = inter.createSkelleton("tmpTI_" + TermInterpretor.getFreshNum(), this.getRanges());
                          this.extraConstraints.add(new MatrixConstraint(inter, interpretations[i], this.fact, ConstraintType.EQ));
                      }
                  } else {
                      interpretations[i] = inter;

                  }
              }



              final long time = System.currentTimeMillis();
              argInterpret = this.argInt.getFAppInterpretations(interpretations, f.getRootSymbol(), this.fact);
              TermInterpretor.log.log(Level.FINEST , "Argument interpretation for " + t.toString() + " took " + Long.toString(System.currentTimeMillis() - time) + "ms\n");

              if (f.getArguments().size() >= 1) {
                  if (!this.rational) {
                      m = this.fact.interpretFApp(this.repres.functionSyms.get(f.getRootSymbol()), Matrix.add(argInterpret));
                      this.cache.put(t, m);
                  } else {
                      // Rational case: The constant part needs to be elevated to proper depth.
                      m = this.repres.functionSyms.get(f.getRootSymbol());
                      if (root.getDepth() > depth) {
                          m =
                                m.multiplyScalar(SimplePolynomial.create(AProVEMath.power(
                                    this.repres.denominator, root.getDepth()
                                        - depth)));
                      }
                      m = this.fact.interpretFApp(m, Matrix.add(argInterpret));
                  }
                  if (this.result != null ) {
                      m = m.specialize(this.result);
                  }
                  return m;
              } else {
                  m = this.fact.interpretFApp(this.repres.functionSyms.get(f.getRootSymbol()), this.fact.createNullMatrix());
                  this.cache.put(t, m);
                  if (this.rational) {
                      // Rational case: The constant part needs to be elevated to proper depth.
                      if (root.getDepth() > depth) {
                          m =
                                m.multiplyScalar(SimplePolynomial.create(AProVEMath.power(
                                    this.repres.denominator, root.getDepth()
                                        - depth)));
                      }
                  }
                  if (this.result != null ) {
                      m = m.specialize(this.result);
                  }
                  return m;
              }
          } else {

              final Matrix[] interpretations = new Matrix[f.getArguments().size()];
              for (int i=0; i<f.getArguments().size(); i++) {
                  final Matrix inter = this.interpretTerm(f.getArgument(i), 1, null,root,depth + 1);

                  if(this.result != null) {
                      if (!this.flatten || this.rational) {
                          interpretations[i] = inter;
                      } else {
                          interpretations[i] = inter.createSkelleton("tmpTI_" + TermInterpretor.getFreshNum(), this.getRanges());
                          this.extraConstraints.add(new MatrixConstraint(inter, interpretations[i], this.fact, ConstraintType.EQ));
                      }
                  } else {
                          interpretations[i] = inter;

                  }
              }

              argInterpret = this.argInt.getDPFAppInterpretations(interpretations, f.getRootSymbol(), this.fact);

              if (f.getArguments().size() >= 1) {
                  if (!this.rational) {
                      m = this.fact.interpretDP(this.repres.dpSyms.get(f.getRootSymbol()), Matrix.add(argInterpret));
                      this.cache.put(t, m);
                  } else {
                      // Rational case: The constant part needs to be elevated to proper depth.
                      m = this.repres.dpSyms.get(f.getRootSymbol());
                      if (root.getDepth() > depth) {
                          m =
                                m.multiplyScalar(SimplePolynomial.create(AProVEMath.power(
                                    this.repres.denominator, root.getDepth()
                                        - depth)));
                      }
                      m = this.fact.interpretDP(m, Matrix.add(argInterpret));
                  }
                  if (this.result != null ) {
                      m = m.specialize(this.result);
                  }
                  return m;
              } else {
                  m = this.fact.interpretDP(this.repres.dpSyms.get(f.getRootSymbol()), this.fact.createDPNullMatrix());
                  this.cache.put(t, m);
                  if (this.rational) {
                      // Rational case: The constant part needs to be elevated to proper depth.
                      if (root.getDepth() > depth) {
                          m =
                                m.multiplyScalar(SimplePolynomial.create(AProVEMath.power(
                                    this.repres.denominator, root.getDepth()
                                        - depth)));
                      }
                  }
                  if (this.result != null ) {
                      m = m.specialize(this.result);
                  }
                  return m;

              }
          }

      } else if (t instanceof TRSVariable) {
          Matrix ret = this.repres.getVarSyms().get(t);
          if (ret == null) {
              final String name = ((TRSVariable)t).getName();
              if (name.startsWith("(>=")) {
                  this.repres.getVarSyms().put((TRSVariable)t, this.fact.createVariableMatrix(name).add(this.interpretTerm( TRSTerm.createVariable(name.substring(3, name.length()-1)))));
              } else {
                  this.repres.getVarSyms().put((TRSVariable)t, this.fact.createVariableMatrix(name));
              }
          }
          ret = this.repres.getVarSyms().get(t);
          if (this.rational) {
              if (root.getDepth() > depth) {
                  ret =
                        ret.multiplyScalar(SimplePolynomial.create(AProVEMath.power(
                            this.repres.denominator, root.getDepth() - depth)));
              }
          }
          return ret;
 // No need to cache variables.
      } else {
          throw new RuntimeException();
      }

  }


  /**
   * Returns the representations used in the underlying order (or order family until specialized).
   * @return
   */
  public SymbolRepresentations getRepresentations () {
      return this.repres;
  }

  /**
   * Returns those constraints the solver additionally needs to correctly solve the order-search.
   * These are in addition to all the constraints directly induced by the rules.
   * @return
   */
  public Set<VarPolyConstraint> getExtraConstraints() {
      final Set<VarPolyConstraint> vpcs = (this.argInt.getExtraConstraints());
      for (final MatrixConstraint mc: this.extraConstraints) {
          vpcs.addAll(mc.getVPCs());
      }
      return vpcs;
  }


  /**
   * If we use individual ranges for every coefficient, return the map of them.
   *
   * @return
   */
  public Map<String, BigIntegerInterval> getRanges() {
      return this.ranges;
  }

  /**
   * Returns the underlying MatrixFactory 
   * TODO: legal?
   * @return
   */
  public MatrixFactory getFact() {
      return this.fact;
  }
  
  /*
  public ArgumentInterpretor getArgInt() {
      return this.argInt;
  }
  */
/**
 * Transform a QDP into a form where a special order can be applied.
 * Currently for performance reasons this blanks through, but if we use MaxMin-Matrices or other case distinguishers this is the place where to do the split.
 * @param origcs
 * @param origdpcs
 * @return
 */
public Triple<Map<Constraint<TRSTerm>, QActiveCondition>, Collection<Constraint<TRSTerm>>, Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>>
       transformQDP(final Map<Constraint<TRSTerm>, QActiveCondition> origcs, final Collection<Constraint<TRSTerm>> origdpcs) {

    // We don't do anything except a deep copy here.

    final Set<Constraint<TRSTerm>> newDPCS = new LinkedHashSet<Constraint<TRSTerm>>();
    final Map<Constraint<TRSTerm>, QActiveCondition> newCS = new LinkedHashMap<Constraint<TRSTerm>, QActiveCondition>();
    final Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations = new LinkedHashMap<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>();


    final Set<Constraint<TRSTerm>> dpcs = new LinkedHashSet<Constraint<TRSTerm>>();
    final Map<Constraint<TRSTerm>, QActiveCondition> cs = new LinkedHashMap<Constraint<TRSTerm>, QActiveCondition>();

    for (final Constraint<TRSTerm> tc: origdpcs) {
        dpcs.add(tc);
    }

    for (final Map.Entry<Constraint<TRSTerm>, QActiveCondition> c: origcs.entrySet()) {
        cs.put(c.getKey(), c.getValue());
    }

    dpcs.iterator();

    for (final Constraint<TRSTerm> c: newDPCS) {
        dpcs.add(c);
    }

    cs.entrySet().iterator();


    for (final Map.Entry<Constraint<TRSTerm>, QActiveCondition> c: newCS.entrySet()) {
        cs.put(c.getKey(), c.getValue());
    }


    return new Triple<Map<Constraint<TRSTerm>, QActiveCondition>, Collection<Constraint<TRSTerm>>, Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>>
      (cs, dpcs, hardCodedRelations);

}
}


/*
 * This is the code if we use max-min matrices. As this is non-modular and currently not needed, it is left commented out.
 */
//
//public Triple<Map<Constraint<Term>, QActiveCondition>, Collection<Constraint<Term>>, Map<Constraint<Term>, Collection<Constraint<Term>>>>
//    transformQDP(Map<Constraint<Term>, QActiveCondition> origcs, Collection<Constraint<Term>> origdpcs) {
//
// Set<Constraint<Term>> newDPCS = new LinkedHashSet<Constraint<Term>>();
// Map<Constraint<Term>, QActiveCondition> newCS = new LinkedHashMap<Constraint<Term>, QActiveCondition>();
// Map<Constraint<Term>, Collection<Constraint<Term>>> hardCodedRelations = new LinkedHashMap<Constraint<Term>, Collection<Constraint<Term>>>();
//
//
// Set<Constraint<Term>> dpcs = new LinkedHashSet<Constraint<Term>>();
// Map<Constraint<Term>, QActiveCondition> cs = new LinkedHashMap<Constraint<Term>, QActiveCondition>();
//
// Set<Constraint<Term>> copydpcs = new LinkedHashSet<Constraint<Term>>();
// Map<Constraint<Term>, QActiveCondition> copycs = new LinkedHashMap<Constraint<Term>, QActiveCondition>();
//
// for (Constraint<Term> tc: origdpcs) {
//     dpcs.add(tc);
// }
//
// for (Map.Entry<Constraint<Term>, QActiveCondition> c: origcs.entrySet()) {
//     cs.put(c.getKey(), c.getValue());
// }
//
// // We now try to find if-like symbols by the following heuristics:
// // If there are rules for a f such that f(t1,...,tn)->t with t <| ti for 2 i's, we consider it to be "if-like" and
// // split the symbol into an f(..., f2(ti1, ti2)).
//
// Map<FunctionSymbol, Set<Integer>> argMap = new LinkedHashMap<FunctionSymbol, Set<Integer>>();
//
// // First iterate over the rules...
// Iterator<Map.Entry<Constraint<Term>,QActiveCondition>> citer = cs.entrySet().iterator();
// while (citer.hasNext()) {
//     Map.Entry<Constraint<Term>, QActiveCondition> entry = citer.next();
//     FunctionApplication leftSide = ((FunctionApplication) (entry.getKey().x));
//     if (leftSide.getRootSymbol().getArity() > 2) {
//         // It makes no sense with lesser arity symbols
//         for (int i=0; i<leftSide.getRootSymbol().getArity(); i++) {
//             if (leftSide.getArgument(i).hasSubterm(entry.getKey().y)) {
//                 // This position is a candidate.
//                 if (argMap.get(leftSide.getRootSymbol()) == null) {
//                     argMap.put(leftSide.getRootSymbol(), new HashSet<Integer>());
//                 }
//                 argMap.get(leftSide.getRootSymbol()).add(i);
//             }
//         }
//     }
// }
//
// // Now see which symbols are actually to be replaced.
// for (Map.Entry<FunctionSymbol, Set<Integer>> e: argMap.entrySet()) {
//     if (e.getValue().size() == 2) {
//         // We got one!
//         // Create a rule mapping the two extracted positions to a fresh symbol, and embed it into the TRS.
//         String n = e.getKey().getName();
//         Variable[] vars = new Variable[e.getKey().getArity()];
//         for (int i=0; i < e.getKey().getArity(); i++) {
//             vars[i] = Variable.createVariable("("+i+")");
//         }
//         ArrayList<Term> l = new ArrayList<Term>(e.getKey().getArity());
//         ArrayList<Term> r = new ArrayList<Term>(e.getKey().getArity()-1);
//         ArrayList<Term> rx = new ArrayList<Term>(2);
//         for (int i=0; i< e.getKey().getArity();i++) {
//             l.add(vars[i]);
//             if (!e.getValue().contains(i)) {
//                 r.add (vars[i]);
//             }
//         }
//         for (Integer i: e.getValue()) {
//             rx.add(vars[i]);
//         }
//         FunctionSymbol r1 = FunctionSymbol.create(n + "(1)",e.getKey().getArity() - 1);
//         FunctionSymbol r2 = FunctionSymbol.create(n + "(2)", 2);
//
//         FunctionApplication rt = FunctionApplication.createFunctionApplication(r2, ImmutableCreator.create(rx));
//         r.add(rt);
//         rt = FunctionApplication.createFunctionApplication(r1, ImmutableCreator.create(r));
//
//         FunctionApplication lt= FunctionApplication.createFunctionApplication(e.getKey(), ImmutableCreator.create(l));
//
//         Rule sub = Rule.create(lt, rt);
//
//         // Now form a new QDP by application of this rule.
//         copydpcs = dpcs; dpcs = new LinkedHashSet<Constraint<Term>>();
//         copycs = cs; cs = new LinkedHashMap<Constraint<Term>, QActiveCondition>();
//
//         for (Constraint<Term> tc: copydpcs) {
//             Constraint<Term> newtc;
//             newtc = Constraint.create(tc.x.rewriteAsOftenAsPossible(sub),tc.y.rewriteAsOftenAsPossible(sub), tc.z);
//
//             if (!(tc.x.equals(newtc.x))) {
//                 transformationMap.put(tc.x, newtc.x);
//             }
//             if (!(tc.y.equals(newtc.y))) {
//                 transformationMap.put(tc.y, newtc.y);
//             }
//             dpcs.add(newtc);
//         }
//
//         for (Map.Entry<Constraint<Term>, QActiveCondition> c: origcs.entrySet()) {
//             Constraint<Term> newtc;
//             newtc = Constraint.create(c.getKey().x.rewriteAsOftenAsPossible(sub),c.getKey().y.rewriteAsOftenAsPossible(sub), c.getKey().z);
//
//             if (!(c.getKey().x.equals(newtc.x))) {
//                 transformationMap.put(c.getKey().x, newtc.x);
//             }
//             if (!(c.getKey().y.equals(newtc.y))) {
//                 transformationMap.put(c.getKey().y, newtc.y);
//             }
//             cs.put(newtc, c.getValue());
//         }
//
//         // and add corresponding matrices to the symbols
//
//         String name = n + "(1)" + "[" + (e.getKey().getArity() - 1) + "]";
//         repres.functionSyms.put(r1, fact.createFSymCoefficientMatrix(name + "_"));
//         repres.multifArgSyms.put(r1, new HashMap<String, Matrix>());
//         Map<Integer, Matrix> args = new LinkedHashMap<Integer, Matrix>();
//
//         for (int i=0; i < e.getKey().getArity() - 1; i++) {
//             args.put(i, fact.createArgSymCoefficientMatrix(name + "{" + (i+1) + "}_"));
//         }
//         repres.functionArgSyms.put(r1, args);
//
//         name = n + "(2)" + "[" + (e.getKey().getArity() - 1) + "]";
//         repres.functionSyms.put(r2, fact.createFSymCoefficientMatrix(name + "_"));
//         repres.multifArgSyms.put(r2, new HashMap<String, Matrix>());
//         args = new LinkedHashMap<Integer, Matrix>();
//
//         for (int i=0; i < 2; i++) {
//             args.put(i, fact.createArgSymCoefficientMatrix(name + "{" + (i+1) + "}_"));
//         }
//         repres.functionArgSyms.put(r2, args);
//
//     }
// }
//
//
//
//
// Iterator<Constraint<Term>> iter = dpcs.iterator();
// // If the underlying order is total...
// if (fact.isTotalOrder()) {
//     // Replace two-Variable instances...
//     while(iter.hasNext()) {
//         Constraint<Term> c = iter.next();
//         Term leftTerm = c.getLeft();
//         Term rightTerm = c.getRight();
//         // Does this contain exactly two variables?
//         if (leftTerm.getVariables().size() == 2) {
//             // If so, get the two variables. Replace the term two times, once by <x, (>=x)>
//             // and once by <(>=x), x>.
//             iter.remove();
//
//             Set<Constraint<Term>> newPairs = new LinkedHashSet<Constraint<Term>>();
//
//             Set<Variable> leftVars = leftTerm.getVariables();
//             Iterator<Variable> iterVars = leftVars.iterator();
//             Map<Variable, Term> varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//             // Add one each to the transformation map for caching purposes
//             if (!(leftTerm.equals(leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(leftTerm, leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//             if (!(rightTerm.equals(rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(rightTerm, rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             newPairs.add (Constraint.create(
//                     leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                     rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                     Relation.GE
//                     ));
//             hardCodedRelations.put(c, newPairs);
//             newDPCS.addAll(newPairs);
//
//         } else if (leftTerm.getVariables().size() == 3) { // or exactly 3?
//             // If so, get the three variables. Replace the term six times, once by <x, (>=x), (>=(>=x))> and all permutations.
//             iter.remove();
//
//             Set<Constraint<Term>> newPairs = new LinkedHashSet<Constraint<Term>>();
//
//             Set<Variable> leftVars = leftTerm.getVariables();
//             Iterator<Variable> iterVars = leftVars.iterator();
//             Map<Variable, Term> varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//             // Add one each to the transformation map for caching purposes
//             if (!(leftTerm.equals(leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(leftTerm, leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//             if (!(rightTerm.equals(rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(rightTerm, rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             newPairs.add (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ));
//
//
//
//             hardCodedRelations.put(c, newPairs);
//             newDPCS.addAll(newPairs);
//
//         }
//
//
//
//
//     }
//
// }
//
// for (Constraint<Term> c: newDPCS) {
//     dpcs.add(c);
// }
//
//
//
// if (fact.isTotalOrder()) {
//
//     Iterator<Map.Entry<Constraint<Term>, QActiveCondition>> csiter = cs.entrySet().iterator();
//     // Replace two-Variable instances...
//     while(csiter.hasNext()) {
//         Map.Entry<Constraint<Term>, QActiveCondition> c = csiter.next();
//         Term leftTerm = c.getKey().getLeft();
//         Term rightTerm = c.getKey().getRight();
//         // Does this contain exactly two variables?
//         if (leftTerm.getVariables().size() == 2) {
//             // If so, get the two variables. Replace the term two times, once by <x, (>=x)>
//             // and once by <(>=x), x>.
//             csiter.remove();
//
//             Set<Variable> leftVars = leftTerm.getVariables();
//             Iterator<Variable> iterVars = leftVars.iterator();
//             Map<Variable, Term> varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             newCS.put (Constraint.create(
//                     leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                     rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                     Relation.GE
//                     ), c.getValue());
//
//             // Add one each to the transformation map for caching purposes
//             if (!(leftTerm.equals(leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(leftTerm, leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//             if (!(rightTerm.equals(rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(rightTerm, rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             newCS.put (Constraint.create(
//                     leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                     rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                     Relation.GE
//                     ), c.getValue());
//         } else if (leftTerm.getVariables().size() == 3) { // or exactly 3?
//             // If so, get the three variables. Replace the term six times, once by <x, (>=x), (>=(>=x))> and all permutations.
//             csiter.remove();
//
//             Set<Constraint<Term>> newPairs = new LinkedHashSet<Constraint<Term>>();
//
//             Set<Variable> leftVars = leftTerm.getVariables();
//             Iterator<Variable> iterVars = leftVars.iterator();
//             Map<Variable, Term> varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             newCS.put (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ),c.getValue());
//
//             // Add one each to the transformation map for caching purposes
//             if (!(leftTerm.equals(leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(leftTerm, leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//             if (!(rightTerm.equals(rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap)))))) {
//                 transformationMap.put(rightTerm, rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))));
//             }
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             newCS.put (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ),c.getValue());
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             newCS.put (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ),c.getValue());
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             newCS.put (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ),c.getValue());
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             newCS.put (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ),c.getValue());
//
//             iterVars = leftVars.iterator();
//             varMap = new LinkedHashMap<Variable, Term>();
//             varMap.put(iterVars.next(), Variable.createVariable("(>=(>=x))"));
//             varMap.put(iterVars.next(), Variable.createVariable("x"));
//             varMap.put(iterVars.next(), Variable.createVariable("(>=x)"));
//             newCS.put (Constraint.create(
//                 leftTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 rightTerm.applySubstitution(Substitution.create(ImmutableCreator.create(varMap))),
//                 Relation.GE
//                 ),c.getValue());
//
//         }
//
//     }
//
// }
//
// for (Map.Entry<Constraint<Term>, QActiveCondition> c: newCS.entrySet()) {
//     cs.put(c.getKey(), c.getValue());
// }
//
//
// return new Triple<Map<Constraint<Term>, QActiveCondition>, Collection<Constraint<Term>>, Map<Constraint<Term>, Collection<Constraint<Term>>>>
//   (cs, dpcs, hardCodedRelations);
//
//}
//}


