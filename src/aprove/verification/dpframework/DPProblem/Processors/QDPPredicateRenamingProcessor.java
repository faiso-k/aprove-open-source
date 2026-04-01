package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * QDP Predicate Renaming processor.
 * Checks whether it finds a DP Symbol which can be renamed into several others,
 * as a certain argument appears only in some different constants.
 * This instance tries to split up exactly one argument.
 *
 * @author Patrick Kabasci
 * @version $Id$
 *
 */
@NoParams
public class QDPPredicateRenamingProcessor extends QDPProblemProcessor {

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        // Allways applicable.
        return true;
    }


    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter) throws AbortionException {

      final Map<FunctionSymbol, Map<Integer, Set<FunctionSymbol>>> instances = new LinkedHashMap<FunctionSymbol, Map<Integer, Set<FunctionSymbol>>>();

      // First get the P signature of the QDP.
      final Set<Rule> P = this.copyMutable(qdp.getP());

      final QDependencyGraph dg = qdp.getDependencyGraph();
      /*dg.

      dg.getGraph()
      */


      final Set<FunctionSymbol> failed = new HashSet<FunctionSymbol>();
      final Set<FunctionSymbol> dpsig = new HashSet<FunctionSymbol> ();

      for (Rule r: P) {
          FunctionSymbol f = r.getLeft().getRootSymbol();
          dpsig.add(f);
          if (!instances.containsKey(f)) {
              instances.put(f, new LinkedHashMap<Integer, Set<FunctionSymbol>> ());
          }
          f = ((TRSFunctionApplication)r.getRight()).getRootSymbol();
          dpsig.add(f);
          if (!instances.containsKey(f)) {
              instances.put(f, new LinkedHashMap<Integer, Set<FunctionSymbol>> ());
          }

          TRSFunctionApplication fApp;
          Map<Integer, Set<FunctionSymbol>> fMap;
          Set<FunctionSymbol> fSet;
          fApp = r.getLeft();
          fMap = instances.get(fApp.getRootSymbol());
          int argCount = fApp.getArguments().size();
          for (int i = 0; i< argCount; i++){
              final TRSTerm t = fApp.getArgument(i);
              if (t instanceof TRSFunctionApplication && ((TRSFunctionApplication)t).getArguments().size() == 0) {
                  fSet = fMap.get(i);
                  if (fSet == null) {
                      fSet = new LinkedHashSet<FunctionSymbol>();
                      fMap.put(i, fSet);
                  }
                  if (fSet != failed) {
                      fSet.add(((TRSFunctionApplication)t).getRootSymbol());
                  }
              } else {
                  fMap.put(i, failed);
              }
          }

          // Get all DPs of the correct form
          fApp = (TRSFunctionApplication)r.getRight();
          fMap = instances.get(fApp.getRootSymbol());
          argCount = fApp.getArguments().size();
          for (int i = 0; i< argCount; i++){
              final TRSTerm t = fApp.getArgument(i);
              if (t instanceof TRSFunctionApplication && ((TRSFunctionApplication)t).getArguments().size() == 0) {
                  fSet = fMap.get(i);
                  if (fSet == null) {
                      fSet = new LinkedHashSet<FunctionSymbol>();
                      fMap.put(i, fSet);
                  }
                  if (fSet != failed) {
                      fSet.add(((TRSFunctionApplication)t).getRootSymbol());
                  }
              } else {
                  fMap.put(i, failed);
              }
          }

      }

      // Now look which symbols are going to be split,
      // and store the replacement symbols.
      final Map<FunctionSymbol, Pair<Integer, Map<FunctionSymbol, FunctionSymbol>>> newMapping = new HashMap<FunctionSymbol, Pair<Integer, Map<FunctionSymbol, FunctionSymbol>>>();
      boolean foundOne = false;

      for (Map.Entry<FunctionSymbol, Map<Integer, Set<FunctionSymbol>>> fS: instances.entrySet()) {
          final Map<Integer, Set<FunctionSymbol>> fMap = instances.get(fS.getKey());
          for (int i=0; i < fS.getKey().getArity(); i++) {
              if (fMap.get(i) != failed) {
                  final Map<FunctionSymbol, FunctionSymbol> redir = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
                  // We are going to extract this argument.
                  for (FunctionSymbol s: fMap.get(i)) {
                       redir.put(s, FunctionSymbol.create (this.generateFreshName(fS.getKey().getName() + "_" + s.getName(), dpsig), fS.getKey().getArity() -1));
                  }
                  newMapping.put(fS.getKey(), new Pair<Integer, Map<FunctionSymbol, FunctionSymbol>>(i, redir));
                  foundOne = true;
              }
          }
      }

      if (foundOne == false) {
          return ResultFactory.unsuccessful();
      }

      // Pass 1:
      // First look up whether we can split the left sides.
      Iterator<Rule> iter = P.iterator();
      final List<Rule> newRules = new ArrayList<Rule>();
      while (iter.hasNext()) {
          final Rule r = iter.next();
          final TRSFunctionApplication fApp = r.getLeft();
          final FunctionSymbol fSym = fApp.getRootSymbol();
          if (newMapping.containsKey(fSym)) {
              final Pair<Integer, Map<FunctionSymbol, FunctionSymbol>> pair = newMapping.get(fSym);
              iter.remove();
              newRules.add(Rule.create(this.buildfApp(fApp, pair.x, pair.y.get(((TRSFunctionApplication)(fApp.getArgument(pair.x))).getRootSymbol())), r.getRight()));
          }
      }
      for (Rule r: newRules) {
          P.add(r);
      }

      // Pass 2:
      // Now look up whether we can split the right sides.
      iter = P.iterator();
      newRules.clear();
      while (iter.hasNext()) {
          final Rule r = iter.next();
          final TRSFunctionApplication fApp = (TRSFunctionApplication) r.getRight();
          final FunctionSymbol fSym = fApp.getRootSymbol();
          if (newMapping.containsKey(fSym)) {
              final Pair<Integer, Map<FunctionSymbol, FunctionSymbol>> pair = newMapping.get(fSym);
              iter.remove();
              newRules.add(
                  Rule.create(
                      r.getLeft(),
                      this.buildfApp(
                          fApp,
                          pair.x,
                          pair.y.get(((TRSFunctionApplication)(fApp.getArgument(pair.x))).getRootSymbol())
                      )
                  )
              );
          }
      }
      for (Rule r: newRules) {
          P.add(r);
      }
      final QDPProblem newQdp = QDPProblem.create(P, qdp.getRwithQ(), qdp.getMinimal());
      final Proof proof = new QDPPredicateRenamingProof(qdp, newQdp);
      return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
    }

    private TRSFunctionApplication buildfApp(TRSFunctionApplication base, int arg, FunctionSymbol newSym) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(newSym.getArity());
        for (int i=0; i<arg; i++) {
            newArgs.add(base.getArgument(i));
        }
        for (int i=arg + 1; i<base.getRootSymbol().getArity(); i++) {
            newArgs.add(base.getArgument(i));
        }
        return TRSTerm.createFunctionApplication(newSym, ImmutableCreator.create(newArgs));
    }

    private boolean contains(Set<FunctionSymbol> set, String name) {
        for (FunctionSymbol fs: set) {
            if (fs.getName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    private Set<Rule> copyMutable(ImmutableSet<Rule> rs) {
        final Set<Rule> ret = new LinkedHashSet<Rule>();
        for (Rule r: rs) {
            ret.add(r);
        }
        return ret;
    }

    private String generateFreshName(String proposal, Set<FunctionSymbol> existing) {
        if (!this.contains(existing, proposal)) {
            return proposal;
        }
        final int i = 0;
        while (true) {
            if (!this.contains(existing, proposal+Integer.toString(i))) {
                return proposal + Integer.toString(i);
            }

        }
    }

    static final class QDPPredicateRenamingProof extends QDPProof {

        QDPProblem origQdp, newQdp;

        QDPPredicateRenamingProof (QDPProblem origQdp, QDPProblem newQdp) {
            this.origQdp = origQdp;
            this.newQdp = newQdp;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "sorry, no export of " + this.getClass().getCanonicalName();
        }

    }

}