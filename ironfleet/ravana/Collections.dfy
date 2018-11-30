module Collections {
  function set_to_multiset<A, B>(m: set<(A, B)>) : multiset<B>
  {
    if |m| == 0 then
      multiset{}
    else (
      var y :| y in m;
      var (a, b) := y;
      var m' := m - {y};
      set_to_multiset(m') + multiset{b}
    )
  }

  predicate {:opaque} keys_match<A, B>(m: map<A, B>, s: set<A>) {
    (forall k : A :: k in m ==> k in s) &&
    (forall k : A :: k in s ==> k in m)
  }

  predicate multiset_adds_one<A>(m: multiset<A>, m1: multiset<A>) {
    |m1| == |m| + 1 &&
    |m1 - m| == 1
  }

  function {:opaque} added_obj<A>(m: multiset<A>, m1: multiset<A>) : A
  requires multiset_adds_one<A>(m, m1)
  {
    var y :| y in (m1 - m);
    y
  }

  function {:opaque} seq_to_multiset<A>(s: seq<A>) : multiset<A>
  {
    if s == [] then
      multiset{}
    else (
      seq_to_multiset(s[0..|s|-1]) + multiset{s[|s|-1]}
    )
  }

  lemma set_to_multiset_induction<A,B>(s : set<(A,B)>, x : (A,B))
  requires !(x in s)
  ensures set_to_multiset(s + {x}) == set_to_multiset(s) + multiset{x.1}
  {
    assert |s + {x}| != 0;

    var m := s + {x};
    assert |m| > 0;
    assert exists y :: y in m &&
          set_to_multiset(m) ==
            (
              var (a, b) := y;
              var m' := m - {y};
              set_to_multiset(m') + multiset{b}
            );

    var z :| z in m && set_to_multiset(m) ==
          (
            var (a, b) := z;
            var m' := m - {z};
            set_to_multiset(m') + multiset{b}
          );
            
    assert set_to_multiset(s + {x})
        == set_to_multiset((s + {x}) - {z}) + multiset{z.1};

    if (z == x) {
      assert (s + {x}) - {x} == s;
      assert set_to_multiset(s + {x})
          == set_to_multiset((s + {x}) - {x}) + multiset{x.1}
          == set_to_multiset(s) + multiset{x.1};
    } else {
      set_to_multiset_induction(s - {z}, x);
      assert set_to_multiset((s - {z}) + {x}) == set_to_multiset(s - {z}) + multiset{x.1};

      assert (s - {z}) + {z} == s;
      set_to_multiset_induction(s - {z}, z);
      assert set_to_multiset((s - {z}) + {z})
          == set_to_multiset(s)
          == set_to_multiset(s - {z}) + multiset{z.1};

      assert (s + {x}) - {z} == (s - {z}) + {x};

      assert set_to_multiset(s + {x})
          == set_to_multiset((s + {x}) - {z}) + multiset{z.1}
          == set_to_multiset((s - {z}) + {x}) + multiset{z.1}
          == set_to_multiset(s - {z}) + multiset{x.1} + multiset{z.1}
          == set_to_multiset(s - {z}) + multiset{z.1} + multiset{x.1}
          == set_to_multiset(s) + multiset{x.1};
    }
  }

  lemma set_diff_impl_multiset_adds_one<A,B>
        (s : set<(A,B)>, s' : set<(A,B)>, key : A, t : B)
  requires s' >= s
  requires s' - s == {(key, t)}
  ensures multiset_adds_one(set_to_multiset(s), set_to_multiset(s'))
  ensures added_obj(set_to_multiset(s), set_to_multiset(s')) == t

  decreases |s|
  {
    if (|s| == 0) {
      assert set_to_multiset(s) == multiset{};
      assert set_to_multiset(s') == multiset{t};
      //var y :| y in set_to_multiset(s') - set_to_multiset(s);

      reveal_added_obj();
      assert exists y :: y in (set_to_multiset(s') - set_to_multiset(s)) &&
                y == added_obj(set_to_multiset(s), set_to_multiset(s'));

      var y :| y in set_to_multiset(s') - set_to_multiset(s) &&
                y == added_obj(set_to_multiset(s), set_to_multiset(s'));

      assert set_to_multiset(s') - set_to_multiset(s) == multiset{t};
      assert y == t;
    } else {
      var y :| y in s;
      assert y in s';
      set_diff_impl_multiset_adds_one(s - {y}, s' - {y}, key, t);

      lemma1(y, s, s', key, t);
      lemma2(y, s, s', key, t);

      lemma3(y, s, s', key, t);

      assert multiset_adds_one(set_to_multiset(s), set_to_multiset(s'));
      reveal_added_obj();
      assert exists z :: z in (set_to_multiset(s') - set_to_multiset(s)) &&
          z == added_obj(set_to_multiset(s), set_to_multiset(s'));
      var z :| z in (set_to_multiset(s') - set_to_multiset(s)) &&
          z == added_obj(set_to_multiset(s), set_to_multiset(s'));
      assert z == t;
    }
  }

  lemma lemma1<A,B>(y: (A,B), s: set<(A,B)>, s': set<(A,B)>, key: A, t: B)
  requires y in s
  requires s' >= s
  requires s' - s == {(key, t)}

  requires multiset_adds_one(set_to_multiset(s-{y}), set_to_multiset(s'-{y}))
  requires added_obj(set_to_multiset(s-{y}), set_to_multiset(s'-{y})) == t

  ensures set_to_multiset(s) == set_to_multiset(s - {y}) + multiset{y.1};
  ensures set_to_multiset(s') == set_to_multiset(s' - {y}) + multiset{y.1};
  {
    assert y in s';
    set_to_multiset_induction(s - {y}, y);
    assert (s - {y}) + {y} == s;
    assert set_to_multiset(s) == set_to_multiset(s - {y}) + multiset{y.1};
    set_to_multiset_induction(s' - {y}, y);
    assert (s' - {y}) + {y} == s';
    assert set_to_multiset(s') == set_to_multiset(s' - {y}) + multiset{y.1};
  }

  lemma lemma2<A,B>(y: (A,B), s: set<(A,B)>, s': set<(A,B)>, key: A, t: B)
  requires y in s
  requires s' >= s
  requires s' - s == {(key, t)}
  requires set_to_multiset(s) == set_to_multiset(s - {y}) + multiset{y.1};
  requires set_to_multiset(s') == set_to_multiset(s' - {y}) + multiset{y.1};

  requires multiset_adds_one(set_to_multiset(s-{y}), set_to_multiset(s'-{y}))
  requires added_obj(set_to_multiset(s-{y}), set_to_multiset(s'-{y})) == t

  ensures |set_to_multiset(s') - set_to_multiset(s)| == 1
  ensures |set_to_multiset(s')| - |set_to_multiset(s)| == 1
  {
    assert |set_to_multiset(s') - set_to_multiset(s)| ==
            |(set_to_multiset(s' - {y}) + multiset{t}) - 
            (set_to_multiset(s - {y}) + multiset{t})|
        == |set_to_multiset(s' - {y}) - set_to_multiset(s - {y})|
        == 1;
    
    assert |set_to_multiset(s')| - |set_to_multiset(s)| ==
            |set_to_multiset(s' - {y}) + multiset{t}| - 
            |set_to_multiset(s - {y}) + multiset{t}|
      ==
            |set_to_multiset(s' - {y})| + |multiset{t}| - 
            (|set_to_multiset(s - {y})| + |multiset{t}|)
      ==
            |set_to_multiset(s' - {y})| - |set_to_multiset(s - {y})|
      == 1; 
  }

  lemma lemma3<A,B>(y: (A,B), s: set<(A,B)>, s': set<(A,B)>, key: A, t: B)
  requires y in s
  requires s' >= s
  requires s' - s == {(key, t)}
  requires set_to_multiset(s) == set_to_multiset(s - {y}) + multiset{y.1};
  requires set_to_multiset(s') == set_to_multiset(s' - {y}) + multiset{y.1};

  requires multiset_adds_one(set_to_multiset(s-{y}), set_to_multiset(s'-{y}))
  requires added_obj(set_to_multiset(s-{y}), set_to_multiset(s'-{y})) == t

  requires |set_to_multiset(s') - set_to_multiset(s)| == 1
  requires |set_to_multiset(s')| - |set_to_multiset(s)| == 1

  ensures set_to_multiset(s') - set_to_multiset(s) == multiset{t};
  {
    assert added_obj(set_to_multiset(s - {y}), set_to_multiset(s' - {y})) == t;

    reveal_added_obj();
    assert t in ((set_to_multiset(s' - {y})) - set_to_multiset(s - {y}));

    assert set_to_multiset(s - {y}) == set_to_multiset(s) - multiset{y.1};
    assert set_to_multiset(s' - {y}) == set_to_multiset(s') - multiset{y.1};

    assert ((set_to_multiset(s' - {y})) - set_to_multiset(s - {y}))
      == (set_to_multiset(s') - multiset{y.1}) - (set_to_multiset(s) - multiset{y.1})
      == set_to_multiset(s') - set_to_multiset(s);

    assert t in set_to_multiset(s') - set_to_multiset(s);

    assert t in ((set_to_multiset(s')) - set_to_multiset(s));

    assert |set_to_multiset(s') - set_to_multiset(s)| == 1;
    one_elem_multiset(set_to_multiset(s') - set_to_multiset(s), t);
    assert set_to_multiset(s') - set_to_multiset(s) == multiset{t};
  }

  lemma one_elem_multiset<A>(s: multiset<A>, t: A)
  requires |s| == 1
  requires t in s
  ensures s == multiset{t}
  {
    assert |s - multiset{t}| == 0;
    assert s - multiset{t} == multiset{};
    assert s == multiset{t} + multiset{};
  }
}
