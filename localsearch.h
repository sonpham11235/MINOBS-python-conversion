#ifndef LOCALSEARCH_H
#define LOCALSEARCH_H 

#include <boost/dynamic_bitset.hpp>
#include "instance.h"
#include "ordering.h"
#include "pivotresult.h"
#include "searchresult.h"
#include "population.h"
#include "resultregister.h"
#include "swapresult.h"
#include "types.h"

enum class Neighbours {
  SWAP,
  INSERT
};

enum class CrossoverType {
  CX,
  OB,
  RK
};

enum class SelectType {
  FIRSTV1,
  FIRSTV2,
  BEST,
  HYBRID,
  OLDHYBRID
};

class LocalSearch {
  public:
    LocalSearch(const Instance &instance);
    const ParentSet &bestParent(const Ordering &ordering, const Types::Bitset pred, int idx) const;
    const ParentSet &bestParentVar(const Types::Bitset pred, const Variable &v) const;
    const ParentSet *bestParentVarWithParent(const Types::Bitset pred, const Variable &a, const Variable &b, const Types::Score orig) const;
    Types::Bitset getPred(const Ordering &ordering, int idx) const;
    Types::Score getBestScore(const Ordering &ordering) const;
    Types::Score getBestScoreWithParents(const Ordering &ordering, std::vector<int> &parents, std::vector<Types::Score> &scores) const;
    Types::Score getBestScoreWithMemo(const Ordering &ordering, Types::Score ***& D, Types::Score ***& E) const;
    Types::Score swappedScoreBack(const Ordering &ordering, int i, Types::Bitset &pred, Types::Score ***& D, Types::Score ***& E);
    Types::Score swappedScoreForward(const Ordering &ordering, int i, Types::Bitset &pred, Types::Score ***& D, Types::Score ***& E);
    Ordering getBestInsertFast(const Ordering &ordering, int pivot, Types::Score initScore, Types::Score ***& D, Types::Score ***& E);
    SearchResult makeResult(const Ordering &ordering) const;
    SearchResult hillClimb(const Ordering &ordering);
    std::vector<int> bestParentIds(const Ordering &ordering);
    Ordering depthSort(const Ordering &ordering);
    SearchResult genetic(float cutoffTime, int INIT_POPULATION_SIZE, int NUM_CROSSOVERS, int NUM_MUTATIONS, int MUTATION_POWER, int DIV_LOOKAHEAD, int NUM_KEEP, float DIV_TOLERANCE, CrossoverType crossoverType, int greediness, Types::Score opt, ResultRegister &rr);
    int getDepth(int m, const std::vector<int> &depth, const Ordering &o, const ParentSet &parent);
    void checkSolution(const Ordering &o);


    Types::Score *** alloc_3d() const;
    void delete_3d(Types::Score ***& arr) const;
  private:
    const Instance &instance;
};

#endif /* LOCALSEARCH_H */
