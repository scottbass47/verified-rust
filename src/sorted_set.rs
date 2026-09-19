//! A sorted, duplicate-free set backed by a vector.

use vstd::prelude::*;

verus! {

#[derive(Debug, Default, PartialEq, Eq)]
pub struct SortedSet {
    values: Vec<i64>,
}

impl SortedSet {
    pub closed spec fn well_formed(self) -> bool {
        forall |i:int, j:int| 
            0 <= i < j < self.values@.len() ==> 
            self.values@[i] < self.values@[j]
    }

    pub closed spec fn as_set(self) -> Set<i64> {
        self.values@.to_set()
    }

    pub fn new() -> (set: Self)
        ensures 
            set.well_formed(),
            set.as_set() == Set::<i64>::empty()
    {
        SortedSet {
            values: Vec::new()
        }
    }

    pub fn as_slice(&self) -> &[i64] {
        &self.values
    }

    pub fn is_empty(&self) -> (result: bool)
        requires
            self.well_formed()
        ensures
            result == self.as_set().is_empty()
    {
        proof {
            self.values@.unique_seq_to_set()
        }
        self.values.is_empty()
    }

    pub fn len(&self) -> (result: usize)
        requires
            self.well_formed()
        ensures
            result == self.as_set().len()
    {
        proof {
            self.values@.unique_seq_to_set()
        }
        self.values.len()
    }

    // [0, 1, 2,  3]
    // [2, 5, 8, 12]
    // lower_bound(1) == 0 since 2 >= 1
    // lower_bound(2) == 0 since 2 >= 2
    // lower_bound(3) == 1 since 5 >= 3
    // lower_bound(20) == 4 since 20 > than everything

    fn lower_bound(&self, value: i64) -> (result: usize) 
        requires
            self.well_formed()
        ensures
            result as int <= self.values@.len(),
            forall |i: int| 0 <= i < result as int ==> self.values@[i] < value,
            forall |i: int| result as int <= i < self.values@.len() ==> value <= self.values@[i]
    {
        let mut lo = 0;
        let mut hi = self.values.len();

        while lo < hi 
            invariant
                self.well_formed(),
                forall |i: int| 0 <= i < lo as int ==> self.values@[i] < value, 
                forall |i: int| hi as int <= i < self.values@.len() ==> value <= self.values@[i], 
                lo <= hi <= self.values.len(),
                decreases (hi - lo),
        {
            let mid = lo + (hi - lo) / 2;
            if self.values[mid] == value {
                return mid
            }
            else if value < self.values[mid] {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }

    pub fn contains(&self, value: i64) -> (result: bool)
        requires
            self.well_formed()
        ensures
            result == self.as_set().contains(value)
    {
        let lo = self.lower_bound(value);
        lo < self.values.len() && self.values[lo] == value
    }


    proof fn seq_insert_to_set(
        s: Seq<i64>,
        i: int,
        value: i64,
    )
        requires
            0 <= i <= s.len(),
        ensures
            s.insert(i, value).to_set()
                =~= s.to_set().insert(value),
    {

        let prefix = s.subrange(0, i);
        let suffix = s.subrange(i, s.len() as int);

        assert(s =~= prefix + suffix);
        assert(s.insert(i, value) =~= prefix.push(value) + suffix);

        vstd::seq_lib::seq_to_set_distributes_over_add(prefix, suffix);
        vstd::seq_lib::seq_to_set_distributes_over_add(
            prefix.push(value),
            suffix,
        );
        prefix.lemma_push_to_set_commute(value);
    }

    pub fn insert(&mut self, value: i64) -> (inserted: bool)
        requires 
            old(self).well_formed()
        ensures
            final(self).well_formed(),
            final(self).as_set() =~= old(self).as_set().insert(value),
            inserted == !old(self).as_set().contains(value)
    {
        let lo = self.lower_bound(value);
        if lo < self.values.len() && self.values[lo] == value{
            false
        }
        else {
            proof {
                Self::seq_insert_to_set(self.values@, lo as int, value);
            }
            self.values.insert(lo, value);
            true
        }
    }

    proof fn seq_remove_to_set(
        s: Seq<i64>,
        i: int,
        value: i64,
    )
        requires
            0 <= i < s.len(),
            s[i] == value,
            forall |x: int, y: int| 
                0 <= x < s.len() && 
                0 <= y < s.len() &&
                s[x] == s[y] ==> x == y
        ensures
            s.remove(i).to_set()
                =~= s.to_set().remove(value),
    {

        let prefix = s.subrange(0, i);
        let suffix = s.subrange(i + 1, s.len() as int);

        assert(s =~= prefix + seq![value] + suffix);
        vstd::seq_lib::seq_to_set_distributes_over_add(prefix, suffix);
    }

    pub fn remove(&mut self, value: i64) -> (removed: bool)
        requires 
            old(self).well_formed()
        ensures
            final(self).well_formed(),
            final(self).as_set() =~= old(self).as_set().remove(value),
            removed == old(self).as_set().contains(value)
    {
        let lo = self.lower_bound(value);
        if lo < self.values.len() && self.values[lo] == value {
            proof {
                Self::seq_remove_to_set(self.values@, lo as int, value);
            }
            self.values.remove(lo);
            true
        } else {
            false
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_empty() {
        let ss = SortedSet::new();
        assert_eq!(ss.len(), 0);
        assert!(ss.is_empty());
        assert_eq!(ss.as_slice(), &[]);
    }

    #[test]
    fn insert_empty_ok() {
        let mut ss = SortedSet::new();
        assert!(ss.insert(1));
        assert!(ss.contains(1));
        assert_eq!(ss.len(), 1);
    }

    #[test]
    fn insert_duplicate() {
        let mut ss = SortedSet::new();
        assert!(ss.insert(1));
        assert!(!ss.insert(1));
        assert!(ss.contains(1));
        assert_eq!(ss.len(), 1);
    }

    #[test]
    fn insert_many() {
        let mut ss = SortedSet::new();
        assert!(ss.insert(5));
        assert!(ss.insert(3));
        assert!(ss.insert(2));
        assert!(ss.insert(1));
        assert!(ss.insert(4));
        assert_eq!(ss.len(), 5);
        assert_eq!(ss.as_slice(), &[1, 2, 3, 4, 5]);
        for i in 1..=5 {
            assert!(ss.contains(i));
        }
    }

    #[test]
    fn insert_remove() {
        let mut ss = SortedSet::new();
        assert!(ss.insert(1));
        assert!(ss.contains(1));
        assert!(ss.remove(1));
        assert!(!ss.contains(1));
        assert!(!ss.remove(1));
    }

    #[test]
    fn contains_missing() {
        let ss = SortedSet::new();
        assert!(!ss.contains(1));
    }
}

}
