#ifndef ORDERING_H
#define ORDERING_H 
#include<iostream>
#include<vector>
#include"instance.h"
#include "types.h"
class Ordering {
  public:
    Ordering() {}
    Ordering(int size);
    void set(const int &index, const int &num);
    int get(const int &index) const;
    friend std::ostream& operator<<(std::ostream &os, const Ordering& o);
    void swap(const int &i, const int &j);
    static Ordering greedyOrdering(const Instance &instance);
    static Ordering greedyOrdering(const Instance &instance, int greediness);
    static Ordering randomOrdering(const Instance &instance);
    int findSmallestConsistentWithOrdering(const int &i, const Instance &instance);
    int findSmallestConsistentWithOrderingRandom(const int &i, const Instance &instance, int greediness);
    void insert(const int &i, const int &j);
    void perturb(int PERTURB_FACTOR);
    int getSize() const;
    bool equals(const Ordering &o) const;
  private:
    std::vector<int> ordering;
    int size;
};

#endif /* ORDERING_H */
