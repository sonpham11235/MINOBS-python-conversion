#include "localsearch.h"
#include "debug.h"
#include <numeric>
#include <utility>
#include <deque>
#include <cmath>
#include "tabulist.h"
#include "util.h"
#include "movetabulist.h"
#include "swaptabulist.h"

LocalSearch::LocalSearch(const Instance &instance) : instance(instance) { 
}

const ParentSet &LocalSearch::bestParent(const Ordering &ordering, const Types::Bitset pred, int idx) const {
  int current = ordering.get(idx);
  const Variable &v = instance.getVar(current);
  return bestParentVar(pred, v);
}

const ParentSet &LocalSearch::bestParentVar(const Types::Bitset pred, const Variable &v) const {
  int numParents = v.numParents();
  for (int i = 0; i < numParents; i++) {
    const ParentSet &p = v.getParent(i);
    if (p.subsetOf(pred)) {
      return p;
    }
  }
  //DBG("PARENT SET NOT FOUND");
  return v.getParent(0); //Should never happen in THeory
}


// Sketchy to use pointeres but we have to use null.. it's possible there is no Var at all.
const ParentSet *LocalSearch::bestParentVarWithParent(const Types::Bitset pred, const Variable &a, const Variable &b, const Types::Score orig) const {
  //const std::vector<int> &candidates = a.parentsWithVarId(b.getId());
  auto candidates_iter = a.parentsWithVarId(b.getId());
  if (candidates_iter == a.parentsWithVar.end()) return NULL;
  const std::vector<int> &candidates = candidates_iter->second;
  int n = candidates.size();
  for (int i = 0; i < n; i++) {
    const ParentSet &p = a.getParent(candidates[i]);
    if (p.getScore() >= orig) break;
    if (p.subsetOf(pred)) {
      return &p;
    }
  }
  //DBG("PARENT SET NOT FOUND");
  return NULL; //Coult happen
}


Types::Bitset LocalSearch::getPred(const Ordering &ordering, int idx) const {
  int n = instance.getN();
  Types::Bitset pred(n, 0);
  for (int i = 0; i < idx; i++) {
    pred[ordering.get(i)] = 1;
  }
  return pred;
}

Types::Score *** LocalSearch::alloc_3d() const{
  int n = instance.getN() + 1, k1 = instance.getNumArcs() + 1, k2 = instance.getNumRoots() + 1;
  Types::Score ***arr = new Types::Score** [n];


  for (int i=0; i<n; i++) {
    arr[i] = new Types::Score* [k1];
    for (int j=0; j<k1; j++) {
      arr[i][j] = new Types::Score[k2];
    }
  }
  return arr;
}

void LocalSearch::delete_3d(Types::Score ***& arr) const {
  int n = instance.getN() + 1, k1 = instance.getNumArcs() + 1, k2 = instance.getNumRoots() + 1;

  for (int i=0; i<n; i++) {
    for (int j=0; j<k1; j++) {
      delete[] arr[i][j];
    }
    delete[] arr[i];
  }
  delete[] arr;
}


Types::Score LocalSearch::getBestScoreWithMemo(const Ordering &ordering, Types::Score ***& D, Types::Score ***& E) const {

  int n = instance.getN(), k1 = instance.getNumArcs(), k2 = instance.getNumRoots();

  int pid[n+1][k1+1][k2+1], psz[n+1][k1+1][k2+1];
  Types::Score psc[n+1][k1+1][k2+1];
  Types::Bitset pred(n, 0);

  for (int i=0; i <= n; i++) {
    for (int j=0; j <= k1; j++) {
      for (int l=0; l <= k2; l++) {
        D[i][j][l] = 223372036854775807LL;
        E[i][j][l] = 223372036854775807LL;
      }
    }
  }


  for (int j=0; j<=k1; j++) {
    D[0][j][0] = 0;
    E[n][j][0] = 0;
  }


  // Compute D[i][j][k] entries
  for (int i=1; i <= n; i++) {
    for (int j=0; j <= k1; j++) {
      for (int l=0; l <= k2; l++) {
        int current = ordering.get(i-1);
        const Variable &v = instance.getVar(current);

        int numParents = v.numParents();
        for (int z = 0; z < numParents; z++) {
          const ParentSet &p = v.getParent(z);
          int w2 = (p.size() == 0) ? 1 : 0;
          if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
            
            if (D[i-1][j-p.size()][l - w2] + p.getScore() < D[i][j][l]) {
              D[i][j][l] = D[i-1][j-p.size()][l - w2] + p.getScore();
            }
          }
        }
      }
    }

    pred[ordering.get(i-1)] = 1;  
  }

  // Compute E[i][j][k]
  Types::Bitset pred2(n, (1<<n) - 1);
  pred2[ordering.get(n-1)] = 0;
  for (int i=n-1; i >= 0; i--) {
    for (int j=0; j <= k1; j++) {
      for (int l = 0; l <= k2; l++) {
        int current = ordering.get(i);
        const Variable &v = instance.getVar(current);


        int numParents = v.numParents();
        for (int z = 0; z < numParents; z++) {
          const ParentSet &p = v.getParent(z);
          int w2 = (p.size() == 0) ? 1 : 0;
          if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
            if (E[i+1][j-p.size()][l-w2] + p.getScore() < E[i][j][l]) {
              E[i][j][l] = E[i+1][j-p.size()][l-w2] + p.getScore();
            }
          }
        }
      }
    }

    if (i != 0) {
      pred[ordering.get(i-1)] = 0;  
    }
  }

/*
  // Sanity check. ----- 
  for (int i=0; i <= n; i++) {
    Types::Score minSc = 223372036854775807LL;

    for (int j = 0; j <= k1; j++) {
      for (int l = 0; l <= k2; l++) {
        minSc = std::min(minSc, D[i][j][l] + E[i][k1-j][k2-l]);
      }
    }

    assert(minSc == D[n][k1][k2]);
    assert(minSc == E[0][k1][k2]);
  }
  //End of sanity check. -----
*/

  return D[n][k1][k2];
}

// New code
Types::Score LocalSearch::getBestScoreWithParents(const Ordering &ordering, std::vector<int> &parents, std::vector<Types::Score> &scores) const {

  int n = instance.getN(), k1 = instance.getNumArcs(), k2 = instance.getNumRoots();
  Types::Score D[n+1][k1+1][k2+1];

  int pid[n+1][k1+1][k2+1], psz[n+1][k1+1][k2+1];
  Types::Score psc[n+1][k1+1][k2+1];
  Types::Bitset pred(n, 0);

  for (int i=0; i <= n; i++) {
    for (int j=0; j <= k1; j++) {
      for (int l=0; l <= k2; l++) {
        D[i][j][l] = 223372036854775807LL;
      }
    }
  }


  for (int j=0; j<=k1; j++) {
    D[0][j][0] = 0;
  }


  // Compute D[i][j][k] entries
  for (int i=1; i <= n; i++) {
    for (int j=0; j <= k1; j++) {
      for (int l=0; l <= k2; l++) {
        int current = ordering.get(i-1);
        const Variable &v = instance.getVar(current);

        int numParents = v.numParents();
        for (int z = 0; z < numParents; z++) {
          const ParentSet &p = v.getParent(z);
          int w2 = (p.size() == 0) ? 1 : 0;
          if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
            
            if (D[i-1][j-p.size()][l - w2] + p.getScore() < D[i][j][l]) {
              D[i][j][l] = D[i-1][j-p.size()][l - w2] + p.getScore();
              pid[i][j][l] = p.getId();
              psc[i][j][l] = p.getScore();
              psz[i][j][l] = p.size();
            }
          }
        }
      }
    }

    pred[ordering.get(i-1)] = 1;  
  }

  if (D[n][k1][k2] != 223372036854775807LL) {
    int j = k1, l = k2;
    for (int i=n; i > 0; i--) {
      parents[ordering.get(i-1)] = pid[i][j][l];
      scores[ordering.get(i-1)] = psc[i][j][l];
      int jj = j;
      j -= psz[i][j][l];
      l -= (psz[i][jj][l] == 0)? 1 : 0;
    }

    assert(j >= 0);
    assert(l == 0);    
  }
  

  return D[n][k1][k2];
}


Types::Score LocalSearch::swappedScoreForward(
const Ordering &ordering, int i, Types::Bitset &pred, Types::Score ***& D, Types::Score ***& E)
{ 
  int n = instance.getN(), k1 = instance.getNumArcs(), k2 = instance.getNumRoots();
  Types::Score bestScore = 223372036854775807LL;  

  for (int j=0; j <= k1; j++) {
    for (int l=0; l <= k2; l++) {
      D[i+1][j][l] = 223372036854775807LL;
      D[i+2][j][l] = 223372036854775807LL; 
    }
  }


  // newordering[i+1]
  for (int j=0; j <= k1; j++) {
    for (int l = 0; l <= k2; l++) {
      int current = ordering.get(i+1);
      const Variable &v = instance.getVar(current);

      int numParents = v.numParents();
      for (int z = 0; z < numParents; z++) {
        const ParentSet &p = v.getParent(z);
        int w2 = (p.size() == 0) ? 1 : 0;
        if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
          if (D[i][j-p.size()][l-w2] + p.getScore() < D[i+1][j][l]) {
            D[i+1][j][l] = D[i][j-p.size()][l-w2] + p.getScore();
          }
        }
      }
    }
  }

  // newordering[i+2]

  pred[ordering.get(i+1)] = 1;

  for (int j=0; j <= k1; j++) {
    for (int l = 0; l <= k2; l++) {
      int current = ordering.get(i);
      const Variable &v = instance.getVar(current);

      int numParents = v.numParents();
      for (int z = 0; z < numParents; z++) {
        const ParentSet &p = v.getParent(z);
        int w2 = (p.size() == 0) ? 1 : 0;


        if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
          if (D[i+1][j-p.size()][l-w2] + p.getScore() < D[i+2][j][l]) {
            D[i+2][j][l] = D[i+1][j-p.size()][l-w2] + p.getScore();
          }
        }
      }
    }
  }

  for (int a = 0; a <= k1; a++) {
    for (int l = 0; l <= k2; l++) {
      bestScore = std::min(bestScore, D[i+2][a][l] + E[i+2][k1-a][k2-l]);
    }
  }

/*
  // Sanity Check
  Ordering newO = ordering;
  newO.swap(i, i+1);
  std::vector<int> parents(n);
  std::vector<Types::Score> scores(n);
  Types::Score sc = getBestScoreWithParents(newO, parents, scores);
  assert(sc == bestScore);
*/

  return bestScore;
}



// Computes the score of the swapped ordering.
// As a side effect, "fixes" E[i-1][...][...] and E[i][...][...]. 
// D[0...i-1] and E[i-1] will remain correct after this method.
Types::Score LocalSearch::swappedScoreBack(
const Ordering &ordering, int i, Types::Bitset &pred, Types::Score ***& D, Types::Score ***& E)
{ 
  int n = instance.getN(), k1 = instance.getNumArcs(), k2 = instance.getNumRoots();
  Types::Score bestScore = 223372036854775807LL;  
  pred[ordering.get(i-1)] = 0;

  for (int j=0; j <= k1; j++) {
    for (int l=0; l <= k2; l++) {
      E[i][j][l] = 223372036854775807LL;
      E[i-1][j][l] = 223372036854775807LL; 
    }
  }


  // newordering[i+1]
  for (int j=0; j <= k1; j++) {
    for (int l = 0; l <= k2; l++) {
      int current = ordering.get(i-1);
      const Variable &v = instance.getVar(current);

      int numParents = v.numParents();
      for (int z = 0; z < numParents; z++) {
        const ParentSet &p = v.getParent(z);
        int w2 = (p.size() == 0) ? 1 : 0;
        if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
          if (E[i+1][j-p.size()][l-w2] + p.getScore() < E[i][j][l]) {
            E[i][j][l] = E[i+1][j-p.size()][l-w2] + p.getScore();
          }
        }
      }
    }
  }

  // newordering[i]

  pred[ordering.get(i)] = 0;

  for (int j=0; j <= k1; j++) {
    for (int l = 0; l <= k2; l++) {
      int current = ordering.get(i);
      const Variable &v = instance.getVar(current);

      int numParents = v.numParents();
      for (int z = 0; z < numParents; z++) {
        const ParentSet &p = v.getParent(z);
        int w2 = (p.size() == 0) ? 1 : 0;
        if (p.subsetOf(pred) && j >= p.size() && l >= w2) {
          if (E[i][j-p.size()][l-w2] + p.getScore() < E[i-1][j][l]) {
            E[i-1][j][l] = E[i][j-p.size()][l-w2] + p.getScore();

          }
        }
      }
    }
  }

  for (int a = 0; a <= k1; a++) {
    for (int l = 0; l <= k2; l++) {
      bestScore = std::min(bestScore, D[i-1][a][l] + E[i-1][k1-a][k2-l]);
    }
  }
  pred[ordering.get(i)] = 1;

/*
  // Sanity check
  Ordering newO = ordering;
  newO.swap(i-1, i);
  std::vector<int> parents(n);
  std::vector<Types::Score> scores(n);
  Types::Score sc = getBestScoreWithParents(newO, parents, scores);
  assert(sc == bestScore);
*/

  return bestScore;
}


// Finds the best insert neighbour of current ordering in O(Cn * k_1 * k_2)
Ordering LocalSearch::getBestInsertFast(const Ordering &ordering, int pivot, Types::Score initScore, Types::Score ***& D, Types::Score ***& E) {
  int n = instance.getN(), k1 = instance.getNumArcs(), k2 = instance.getNumRoots();
  Types::Score bestScore = initScore;
  Ordering bestOrdering = ordering;

  Types::Bitset forwardPred = getPred(ordering, pivot);
  Types::Bitset backwardPred(forwardPred);
  forwardPred[ordering.get(pivot)] = 0;

  Ordering forwardModified(ordering);
  Ordering backwardModified(ordering);

  Types::Score ***forwardD = D;
  Types::Score ***forwardE = E;


  Types::Score ***backwardD = alloc_3d();
  Types::Score ***backwardE = alloc_3d();

  // Make a complete copy of D, E.
  for (int i=0; i <= n; i++) {
    for (int j=0; j<= k1; j++) {
      for (int l=0; l<= k2; l++) {
        backwardD[i][j][l] = forwardD[i][j][l];
        backwardE[i][j][l] = forwardE[i][j][l];
      }
    }
  }

  for (int i = pivot - 1; i >= 0; i--) {

    Types::Score newScore = swappedScoreBack(backwardModified, i+1, backwardPred, D, E);
    backwardModified.swap(i, i+1);
    if (newScore < bestScore) {
      bestScore = newScore;
      bestOrdering = backwardModified;
    }
  }

  for (int i = pivot; i < n-1; i++) {
    Types::Score newScore = swappedScoreForward(forwardModified, i, forwardPred, D, E);
    forwardModified.swap(i, i+1);

    if (newScore < bestScore) {
      bestScore = newScore;
      bestOrdering = forwardModified;
    }
  }

/*
  // Sanity check
  std::vector<int> parents(n);
  std::vector<Types::Score> scores(n);
  Types::Score sc = getBestScoreWithParents(bestOrdering, parents, scores);
  assert(sc == bestScore);
*/

  delete_3d(backwardD);
  delete_3d(backwardE);

  return bestOrdering;
}

SearchResult LocalSearch::hillClimb(const Ordering &ordering) {
  bool improving = false;
  int n = instance.getN(), k1 = instance.getNumArcs(), k2 = instance.getNumRoots();
  int steps = 0;
  std::vector<int> positions(n);
  Ordering cur(ordering);

  Types::Score *** D = alloc_3d(), *** E = alloc_3d();
  Types::Score curScore = getBestScoreWithMemo(cur, D, E);
  std::iota(positions.begin(), positions.end(), 0);

  do {
    improving = false;
    std::random_shuffle(positions.begin(), positions.end());
    for (int s = 0; s < n && !improving; s++) {
      int pivot = positions[s];
      Ordering result = getBestInsertFast(cur, pivot, curScore, D, E);
      Types::Score newScore = getBestScoreWithMemo(result, D, E);

      if (newScore < curScore) {
        steps += 1;
        improving = true;
        cur = result;
        curScore = newScore;
      }
    }
  } while(improving);

  delete_3d(D);
  delete_3d(E);

  return SearchResult(curScore, cur);
}

std::vector<int> LocalSearch::bestParentIds(const Ordering &ordering) {
  int n = instance.getN();
  Types::Bitset pred(n, 0);
  std::vector<int> parents(0);
  for (int i = 0; i < n; i++) {
    parents.push_back(bestParent(ordering, pred, i).getId());
    pred[ordering.get(i)] = 1;
  }
  return parents;
}

SearchResult LocalSearch::makeResult(const Ordering &ordering) const {
  int n = instance.getN();
  Types::Bitset pred(n, 0);
  std::vector<int> parents(0);
  Types::Score score = 0;
  for (int i = 0; i < n; i++) {
    score += bestParent(ordering, pred, i).getScore();
    pred[ordering.get(i)] = 1;
  }
  return SearchResult(score, ordering);
}

Ordering LocalSearch::depthSort(const Ordering &ordering) {
  std::vector<int> parentIds = bestParentIds(ordering);
  int n = instance.getN();
  std::vector<int> depth(n);
  for (int i = 0; i < n; i++) {
    const Variable &v = instance.getVar(ordering.get(i));
    ParentSet p = v.getParent(parentIds[i]);
    int d = getDepth(i, depth, ordering, p);
    depth[i] = d;
    DBG("Depth: " << d);

  }
  std::vector<std::pair<int, int>> depth_var;
  for (int i = 0; i < n; i++) {
    depth_var.push_back(std::make_pair(depth[i], ordering.get(i)));
  }
  std::sort(depth_var.begin(), depth_var.end());
  Ordering ret(n);
  for (int i = 0; i < n; i++) {
    ret.set(i, depth_var[i].second);
  }
  return ret;
}

int LocalSearch::getDepth(int m, const std::vector<int> &depth, const Ordering &ordering, const ParentSet &parent) {
  int n = instance.getN();
  std::vector<int> inDepth(n, n-1);

  for (int i = 0; i < m; i++) {
    inDepth[ordering.get(i)] = depth[i];
  }
  int d = 0;
  for (int i = 0; i < n; i++) {
    if (parent.hasElement(i)) {
      if (d < inDepth[i] + 1) {
        d = inDepth[i] + 1;
      }
    }
  }
  return d;
}

SearchResult LocalSearch::genetic(float cutoffTime, int INIT_POPULATION_SIZE, int NUM_CROSSOVERS, int NUM_MUTATIONS,
    int MUTATION_POWER, int DIV_LOOKAHEAD, int NUM_KEEP, float DIV_TOLERANCE, CrossoverType crossoverType, int greediness, Types::Score opt, ResultRegister &rr) {
  int n = instance.getN();
  SearchResult best(Types::SCORE_MAX, Ordering(n));
  std::deque<Types::Score> fitnesses;
  Population population(*this);
  int numGenerations = 1;
  std::cout << "Time: " << rr.check() << " Generating initial population" << std::endl;
  for (int i = 0; i < INIT_POPULATION_SIZE; i++) {
    SearchResult o;
    if (greediness == -1) {
      o = hillClimb(Ordering::randomOrdering(instance));
    } else {
      o = hillClimb(Ordering::greedyOrdering(instance, greediness));
    }
  /*
   * Added to show a solution early.
   */
  std::cout << "Time: " << rr.check() <<  " i = " << i << " The score is: " << o.getScore() << std::endl;
    rr.record(o.getScore(), o.getOrdering());
    population.addSpecimen(o);
  }
  std::cout << "Done generating initial population" << std::endl;
  do {
    //std::cout << "Time: " << rr.check() << " Starting generation " << numGenerations << std::endl;
    //DBG(population);
    std::vector<SearchResult> offspring;
    population.addCrossovers(NUM_CROSSOVERS, crossoverType, offspring);
    //DBG(population);
    population.mutate(NUM_MUTATIONS, MUTATION_POWER, offspring);
    //DBG(population);
    population.append(offspring);
    population.filterBest(INIT_POPULATION_SIZE);
    DBG(population);
    Types::Score fitness = population.getAverageFitness();
    fitnesses.push_back(fitness);
    if (fitnesses.size() > DIV_LOOKAHEAD) {
      Types::Score oldFitness = fitnesses.front();
      fitnesses.pop_front();
      float change = std::abs(((float)fitness-(float)oldFitness)/(float)oldFitness);
      if (change < DIV_TOLERANCE && DIV_TOLERANCE != -1) {
        DBG("Diversification Step. Change: " << change << " Old: " << oldFitness << " New: " << fitness);
        population.diversify(NUM_KEEP, instance);
        fitnesses.clear();
      }
    }
    DBG("Fitness: " << population.getAverageFitness());
    SearchResult curBest = population.getSpecimen(0);
    Types::Score curScore = curBest.getScore();
    if (curScore < best.getScore()) {
      std::cout << "Time: " << rr.check() <<  " The best score at this iteration is: " << curScore << std::endl;
      rr.record(curBest.getScore(), curBest.getOrdering());
      best = curBest;
    }
    numGenerations++;
  } while (rr.check() < cutoffTime);
  std::cout << "Generations: " << numGenerations << std::endl;
  return best;
}

void LocalSearch::checkSolution(const Ordering &o) {
  int n = instance.getN();
  std::vector<int> parents(n);
  std::vector<Types::Score> scores(n);
  getBestScoreWithParents(o, parents, scores);
  long long scoreFromScores = 0;
  long long scoreFromParents = 0;
  std::vector<int> inverse(n);
  for (int i = 0; i < n; i++) {
    inverse[o.get(i)] = i;
  }

  bool valid = true;
  for (int i = 0; i < n; i++) {
    int var = o.get(i);
    const Variable &v = instance.getVar(var);
    const ParentSet &p = v.getParent(parents[var]);
    const std::vector<int> &parentVars = p.getParentsVec();
    std::string parentsStr = "";
    bool before = true;
    for (int j = 0; j < parentVars.size(); j++) {
      parentsStr += std::to_string(parentVars[j]) + " ";
      before = before && (inverse[parentVars[j]] < i);
    }
    valid &= before;
    scoreFromParents += p.getScore();
    scoreFromScores += scores[var];
    std::cout << "Ordering[" << i << "]\t= "<< var << "\tScore:\t" << scores[var] << "\tParents:\t{ " << parentsStr << "}\tValid: " << before << std::endl;
  }
  std::cout << "Total Score: " << scoreFromScores << " " << scoreFromParents << std::endl;
  std::string validStr = valid ? "Good" : "Bad";
  std::cout << "Validity Check: " << validStr << std::endl;
}
