use vstd::prelude::*;
use vstd::multiset::*;
use vstd::seq::*;

verus! {

#[derive(Debug, Default, PartialEq, Eq)]
pub struct MinHeap {
    values: Vec<i64>
}

impl MinHeap {
    spec fn parent_index(i: int) -> int 
        recommends 
            0 < i
    {
        (i - 1) / 2
    }

    spec fn left_index(i: int) -> int 
    {
        2*i + 1
    }

    spec fn right_index(i: int) -> int 
    {
        2*i + 2
    }

    pub closed spec fn well_formed(self) -> bool {
        Self::well_formed_vec(self.values)
    }

    #[verifier::inline]
    spec fn edge_ok(v: Seq<i64>, child: int) -> bool 
        recommends
            0 < child < v.len()
    {
        v[Self::parent_index(child)] <= v[child]
    }

    spec fn well_formed_vec(vec: Vec<i64>) -> bool {
        let v = vec@;
        let len = v.len();

        forall |child: int| #![auto]
            0 < child < len ==> Self::edge_ok(v, child)
    }

    pub closed spec fn as_multi(self) -> Multiset<i64> {
        self.values@.to_multiset()
    }

    pub fn new() -> (result: Self)
        ensures
            result.well_formed(),
            result.as_multi() =~= Multiset::<i64>::empty()
    {
        let v = Vec::new();
        proof {
            v@.to_multiset_ensures();
        }
        MinHeap {
            values: v
        }
    }

    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self.as_multi().is_empty()
    {
        proof {
            self.values@.to_multiset_ensures();
        }
        self.values.is_empty()
    }

    pub fn len(&self) -> (result: usize)
        ensures
            result == self.as_multi().len()
            
    {
        proof {
            self.values@.to_multiset_ensures();
        }
        self.values.len()
    }

    proof fn root_le_index(self, i: int) 
        requires
            self.well_formed(),
            0 <= i < self.values@.len()
        ensures
            self.values@[0] <= self.values@[i],
        decreases i
    {
        if i == 0 {
        } else {
            self.root_le_index(Self::parent_index(i));
        }
    }

    proof fn root_is_min(self)
        requires
            self.well_formed()
        ensures
            forall |i: int| 
                0 <= i < self.values@.len() ==>
                self.values@[0] <= #[trigger] self.values@[i]
    {
        assert forall |i:int| 
            0 <= i < self.values@.len() implies
            self.values@[0] <= #[trigger] self.values@[i]
        by {
            self.root_le_index(i)
        }
    }

    pub open spec fn is_min(v: i64, set: Multiset<i64>) -> bool {
            set.contains(v) && 
            forall |i: i64|
                set.contains(i) ==> v <= i
    }

    pub fn peek_min(&self) -> (result: Option<i64>)
        requires
            self.well_formed()
        ensures
            match result {
                None => self.as_multi().is_empty(),
                Some(v) => Self::is_min(v, self.as_multi())
            }
    {
        proof {
            self.values@.to_multiset_ensures();
        }
        if self.values.len() == 0 {
            None
        } else {
            proof {
                self.root_is_min();
            }
            Some(self.values[0])
        }
    }

    fn parent(i: usize) -> (result: usize)
        requires
            0 < i
        ensures
            result as int == Self::parent_index(i as int)
    {
        (i - 1) / 2
    }

    fn left(i: usize) -> (result: usize)
        requires
            2 * i + 1 <= usize::MAX
        ensures
            result as int == Self::left_index(i as int)
    {
        2 * i + 1
    }

    fn right(i: usize) -> (result: usize)
        requires
            2 * i + 2 <= usize::MAX
        ensures
            result as int == Self::right_index(i as int)
    {
        2 * i + 2
    }

    fn swap(&mut self, i: usize, j: usize) 
        requires
            0 <= i < self.values@.len(),
            0 <= j < self.values@.len(),
        ensures
            final(self).values@ =~= old(self).values@
                .update(i as int, old(self).values@[j as int])
                .update(j as int, old(self).values@[i as int]),
            final(self).as_multi() =~= old(self).as_multi()
    {
        proof {
            broadcast use vstd::seq_lib::to_multiset_update;
            self.values@.to_multiset_ensures();
        }
        let tmp = self.values[j];
        self.values[j] = self.values[i];
        self.values[i] = tmp;
    }

    proof fn lemma_sift_up_ok(v: Seq<i64>, i: int, p: int) 
        requires
            // Parent and child have valid indexes
            0 < i < v.len(),
            0 <= p < v.len(),

            // Really is parent -> child
            p == Self::parent_index(i),

            // Only broken edge is the parent of i
            Self::almost_ok_up(v, i),

            // p is LE both of i's children
            Self::around_ok(v, i),

            // i is actually smaller than it's parent
            v[i] < v[p],

        ensures
            // After swapping, only potentially broken edges leave c
            Self::almost_ok_up(Self::swapped(v, i, p), p),

            // The defect at c is safe to move down
            Self::around_ok(Self::swapped(v, i, p), p),
    {
    }

    fn sift_up(&mut self, idx: usize) 
        requires
            idx < self.values@.len(),
            Self::almost_ok_up(self.values@, idx as int),
            Self::around_ok(self.values@, idx as int),
        ensures
            final(self).well_formed(),
            final(self).as_multi() =~= old(self).as_multi()
    {
        let mut i = idx;
        while i > 0 && self.values[i] < self.values[Self::parent(i)] 
            invariant
                i < self.values@.len(),
                self.values.len() == old(self).values.len(),
                Self::almost_ok_up(self.values@, i as int),
                Self::around_ok(self.values@, i as int),
                self.as_multi() =~= old(self).as_multi()
            decreases i
        {
            let p = Self::parent(i);
            proof {
                Self::lemma_sift_up_ok(self.values@, i as int, p as int);
            }
            self.swap(p, i);
            i = p;
        }
    }

    pub fn push(&mut self, value: i64)
        requires
            old(self).well_formed()
        ensures
            final(self).well_formed(),
            final(self).as_multi() =~= old(self).as_multi().insert(value)
    {
        proof {
            self.values@.to_multiset_ensures();
        }
        self.values.push(value);
        self.sift_up(self.values.len() - 1);
    }

    broadcast proof fn lemma_drop_last_remove<A>(seq: Seq<A>) 
        requires
            seq.len() > 0
        ensures
            #![trigger seq.drop_last()]
            seq.drop_last() =~= seq.remove(seq.len() as int - 1)
    {
    }

    proof fn lemma_swap_remove<A>(seq: Seq<A>, i: int) 
        requires
            0 <= i < seq.len()
        ensures
            seq.update(i, seq.last()).drop_last().to_multiset() 
                =~= 
            seq.to_multiset().remove(seq[i])

    {
        broadcast use vstd::seq_lib::to_multiset_update;
        broadcast use vstd::seq_lib::to_multiset_remove;
        broadcast use MinHeap::lemma_drop_last_remove;
    }


    spec fn almost_ok_up(v: Seq<i64>, broken_child: int) -> bool
        recommends
            0 <= broken_child < v.len()
    {
        forall |child: int|
            0 < child < v.len() && child != broken_child
            ==> Self::edge_ok(v, child)
    }

    spec fn around_ok(v: Seq<i64>, i: int) -> bool
    {
        i > 0 ==>
            forall |child: int|
                0 < child < v.len() && Self::parent_index(child) == i
                ==> v[Self::parent_index(i)] <= v[child]
    }

    spec fn almost_ok_down(v: Seq<i64>, broken_parent: int) -> bool
        recommends
            0 <= broken_parent <= v.len()
    {
        forall |child: int|
            0 < child < v.len() && Self::parent_index(child) != broken_parent
            ==> Self::edge_ok(v, child)
    }

    spec fn swapped(v: Seq<i64>, i: int, j: int) -> Seq<i64> {
        v.update(i, v[j]).update(j, v[i])
    }

    proof fn lemma_sift_down_ok(v: Seq<i64>, i: int, c: int) 
        requires
            0 <= i < v.len(),
            0 < c < v.len(),
            Self::parent_index(c) == i,
            Self::almost_ok_down(v, i),
            Self::around_ok(v, i),

            // c is the smallest child of i
            forall |sibling: int|
                0 < sibling < v.len() && Self::parent_index(sibling) == i ==>
                v[c] <= v[sibling],

            // c is actually smaller than i
            v[c] < v[i],

        ensures
            Self::almost_ok_down(Self::swapped(v, i, c), c),
            Self::around_ok(Self::swapped(v, i, c), c),
    {
    }

    fn sift_down(&mut self, idx: usize) 
        requires
            idx == 0,
            Self::almost_ok_down(old(self).values@, idx as int),
        ensures
            final(self).well_formed(),
            final(self).as_multi() =~= old(self).as_multi()
    {

        let mut i = idx;
        while i < self.values.len() / 2
            invariant
                Self::almost_ok_down(self.values@, i as int),
                Self::around_ok(self.values@, i as int),
                self.as_multi() =~= old(self).as_multi()

            ensures
                Self::well_formed_vec(self.values)

            decreases self.values.len() - i
        {
            let l = Self::left(i);
            let r = Self::right(i);
            let mut smallest = i;

            if l < self.values.len() && self.values[l] < self.values[smallest] {
                smallest = l;
            }
            if r < self.values.len() && self.values[r] < self.values[smallest] {
                smallest = r;
            }
            if smallest == i {
                break;
            }

            proof {
                Self::lemma_sift_down_ok(self.values@, i as int, smallest as int);
            }
            self.swap(i, smallest);
            i = smallest;
        }
    }


    pub fn pop(&mut self) -> (result: i64)
        requires
            old(self).as_multi().len() > 0,
            old(self).well_formed()
        ensures
            final(self).well_formed(),
            final(self).as_multi() =~= old(self).as_multi().remove(result),
            Self::is_min(result, old(self).as_multi())
    {
        proof {
            self.values@.to_multiset_ensures();
            self.root_is_min();
            Self::lemma_swap_remove(self.values@, 0); 
        }

        let result = self.values.swap_remove(0);
        self.sift_down(0);
        result
    }
}

#[cfg(test)]
mod tests{
    use super::*;

    #[test]
    fn empty_ok() {
        let h = MinHeap::new();
        assert!(h.is_empty());
        assert_eq!(h.len(), 0);
    }

}
}
