/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import ApplicationStatements

/-!
# The order-theoretic part of Lemma 4.8

All statements use the independently defined `SeifertApplicationStatement.complexity`
and `Values`. The geometric finiteness assertion (i) is an input. The conclusions are
the finite bounded intersections and order-type bounds of (ii), the well-order and
order-type bound of (iii), and countability (iv). No positivity of area is needed.
The closed/discrete topology assertion in (ii) is not part of this order-theoretic API.
-/

noncomputable section
universe u
namespace SeifertApplicationStatement
variable {V : Type u} {g : V → ℕ} {A : V → ℝ}

/-- Lemma 4.8(i), with every real cutoff. With positive areas this is equivalent to
the paper's restriction to positive cutoffs, since a nonpositive sublevel is empty. -/
def FiniteFibres (g : V → ℕ) (A : V → ℝ) : Prop :=
  ∀ (h : ℕ) (a : ℝ), ({v | g v = h ∧ A v ≤ a} : Set V).Finite

/-- With the positive areas of Definition 4.7, the real-cutoff input is precisely
Lemma 4.8(i): nonpositive cutoffs contribute only the empty set. -/
theorem finiteFibres_iff_positive_cutoffs (hpos : ∀ v, 0 < A v) :
    FiniteFibres g A ↔
      ∀ (h : ℕ) (a : ℝ), 0 < a → ({v | g v = h ∧ A v ≤ a} : Set V).Finite := by
  constructor
  · intro hf h a _
    exact hf h a
  · intro hf h a
    by_cases ha : 0 < a
    · exact hf h a ha
    · apply Set.finite_empty.subset
      rintro v ⟨_, hv⟩
      exact False.elim ((not_lt_of_ge (le_trans hv (le_of_not_gt ha))) (hpos v))

/-- The set `W_h` in Lemma 4.8(ii), with its induced real order. -/
def AreaValues (g : V → ℕ) (A : V → ℝ) (h : ℕ) : Set ℝ :=
  {a | ∃ v, g v = h ∧ A v = a}

/-- Lemma 4.8(ii), first sentence of its proof: the bounded area-value set is the
image of the finite set in (i). The interval is `(-∞, a]`, without positive area. -/
theorem areaValues_finite_Iic (hf : FiniteFibres g A) (h : ℕ) (a : ℝ) :
    (AreaValues g A h ∩ Set.Iic a).Finite := by
  apply ((hf h a).image A).subset
  rintro b ⟨⟨v, hv, rfl⟩, hb⟩
  exact ⟨v, ⟨hv, hb⟩, rfl⟩

/-- Rank within one genus: the number of distinct, strictly smaller attained areas.
Finiteness of the predecessor set follows from (i), so ties are counted only once. -/
def areaRank (g : V → ℕ) (A : V → ℝ) (h : ℕ) (a : ℝ) : ℕ :=
  (AreaValues g A h ∩ Set.Iio a).ncard

/-- Strict increase of the predecessor count on actual area values. -/
theorem areaRank_strictMono (hf : FiniteFibres g A) (h : ℕ) :
    StrictMono (fun a : AreaValues g A h => areaRank g A h a.val) := by
  intro a b hab
  change a.val < b.val at hab
  apply Set.ncard_lt_ncard
  · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro c hc
      exact ⟨hc.1, lt_trans (show c < a.val from hc.2) hab⟩
    · intro he
      have ha : a.val ∈ AreaValues g A h ∩ Set.Iio b.val := ⟨a.property, hab⟩
      rw [← he] at ha
      exact lt_irrefl a.val (show a.val < a.val from ha.2)
  · exact (areaValues_finite_Iic hf h b.val).subset
      (fun c hc => ⟨hc.1, le_of_lt (show c < b.val from hc.2)⟩)

/-- Lemma 4.8(ii), order type at most omega: `W_h` order-embeds into the naturals.
This encodes the order-type claim without changing the induced order on `W_h`. -/
def areaValues_orderEmbedding (hf : FiniteFibres g A) (h : ℕ) :
    AreaValues g A h ↪o ℕ :=
  OrderEmbedding.ofStrictMono _ (areaRank_strictMono hf h)

/-- An attained lexicographic value has an attained area in its own genus. -/
theorem value_area_mem (x : Values g A) :
    (ofLex x.val).2 ∈ AreaValues g A (ofLex x.val).1 := by
  obtain ⟨v, hv⟩ := x.property
  rw [← hv]
  exact ⟨v, rfl, rfl⟩

/-- Lemma 4.8(iii): the lexicographic ordered sum of the `W_h` embeds into
`N ×ₗ N`, of order type omega squared. The source is the actual `Values` subtype. -/
def values_orderEmbedding (hf : FiniteFibres g A) : Values g A ↪o ℕ ×ₗ ℕ :=
  OrderEmbedding.ofStrictMono
    (fun x => toLex ((ofLex x.val).1, areaRank g A (ofLex x.val).1 (ofLex x.val).2))
    (by
      intro x y hxy
      change toLex (ofLex x.val) < toLex (ofLex y.val) at hxy
      apply Prod.Lex.toLex_lt_toLex.mpr
      rcases Prod.Lex.toLex_lt_toLex.mp hxy with hg | ⟨hg, ha⟩
      · exact Or.inl hg
      · refine Or.inr ⟨hg, ?_⟩
        have hx := value_area_mem x
        rw [hg] at hx
        have hr := areaRank_strictMono hf (ofLex y.val).1
          (a := ⟨(ofLex x.val).2, hx⟩) (b := ⟨(ofLex y.val).2, value_area_mem y⟩) ha
        simpa only [hg] using hr)

/-- Lemma 4.8(iii), "W is well-ordered ... in particular every non-empty subset
of W has a least element": strict order is well-founded on the induced `Values`. -/
theorem values_wellFounded (hf : FiniteFibres g A) :
    WellFounded ((· < ·) : Values g A → Values g A → Prop) :=
  (values_orderEmbedding hf).wellFounded wellFounded_lt

/-- The last displayed union in the proof of Lemma 4.8(iv). Every real area has
a natural upper bound, regardless of its sign. This covers vertices, including ties. -/
theorem vertices_eq_iUnion (g : V → ℕ) (A : V → ℝ) :
    (Set.univ : Set V) = ⋃ h : ℕ, ⋃ n : ℕ, {v | g v = h ∧ A v ≤ (n : ℝ)} := by
  ext v
  simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
  obtain ⟨n, hn⟩ := exists_nat_ge (A v)
  exact ⟨g v, n, rfl, hn⟩

/-- Lemma 4.8(iv), "IS(K) has countably many vertices": a countable union of
the finite vertex sets in (i). Counting distinct values alone would not suffice. -/
theorem vertices_countable (hf : FiniteFibres g A) : Countable V := by
  apply Set.countable_univ_iff.mp
  rw [vertices_eq_iUnion g A]
  exact Set.countable_iUnion (fun h => Set.countable_iUnion (fun n => (hf h n).countable))

end SeifertApplicationStatement
