#include "parentset.h"
#include "debug.h"
ParentSet::ParentSet(Types::Score score, Types::Bitset parents, int var, int id, std::vector<int> parentsVec) :
  score(score), parents(parents), var(var), id(id), parentsVec(parentsVec) { }

bool ParentSet::hasElement(int k) const {
  return parents[k];
}

int ParentSet::getVar() const {
  return var;
}

std::ostream& operator<<(std::ostream &os, const ParentSet& p) {
  os << "Score : " << p.score << " ParentSet: " << p.parents << " Child: " << p.var << " Id: " << p.id;
  return os;
}

Types::Score ParentSet::getScore() const {
  return score;
}

bool ParentSet::subsetOf(const Types::Bitset &set) const {
  return (set & parents) == parents;
}

int ParentSet::size() const {
  return parents.count();
}

void ParentSet::setId(const int &i) {
  id = i;
}

int ParentSet::getId() const {
  return id;
}

const std::vector<int> &ParentSet::getParentsVec() const {
  return parentsVec;
}
