import PoincareConjecture.Proofs.M02.Topology.FiniteGeometricCoordinates
import PoincareConjecture.Proofs.M02.Topology.FiniteFlagCoordinates









set_option autoImplicit false

open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {I : Type v} [PartialOrder I] [Fintype I]

private theorem order_simplex_support_max
    (z : (finiteOrderComplex I).space) :
    ∃ j : I, z.val j ≠ 0 ∧ ∀ i, z.val i ≠ 0 → i ≤ j := by
  classical
  let s := Finset.univ.filter (fun i => z.val i ≠ 0)
  have hz := (finiteOrderComplex_space I z.val).mp z.property
  have hs : s.Nonempty := by
    by_contra h
    have hzero (i : I) : z.val i = 0 := by
      by_contra hi
      exact h ⟨i, by simp [s, hi]⟩
    have heq := hz.2.1
    simp only [hzero, Finset.sum_const_zero] at heq
    exact zero_ne_one heq
  obtain ⟨j, hj, hmax⟩ := Finset.exists_maximal hs
  have hzj : z.val j ≠ 0 := (Finset.mem_filter.mp hj).2
  refine ⟨j, hzj, ?_⟩
  intro i hi
  rcases hz.2.2 i j hi hzj with hij | hji
  · exact hij
  · exact hmax (by simp [s, hi]) hji

theorem finiteOrderComplexMap_injective_of_geometric_faces
    (K : Geometry.SimplicialComplex Real E) (s : I → Finset E)
    (hs : ∀ i, s i ∈ K.faces)
    (horder : ∀ i j, i ≤ j ↔ s i ⊆ s j)
    (w : I → E → Real)
    (hw : ∀ i x, 0 ≤ w i x)
    (hwpos : ∀ i x, 0 < w i x ↔ x ∈ s i)
    (hwsum : ∀ i, ∑ x ∈ s i, w i x = 1) :
    Function.Injective (finiteOrderComplexMap I (fun i => ∑ x ∈ s i, w i x • x)) := by
  classical
  have hwzero (i : I) (x : E) (hx : x ∉ s i) : w i x = 0 :=
    le_antisymm (not_lt.mp (fun h => hx ((hwpos i x).mp h))) (hw i x)
  let weights (z : (finiteOrderComplex I).space) : E → Real :=
    ∑ i, z.val i • w i
  have hweights (z : (finiteOrderComplex I).space) (j : I)
      (hj : ∀ i, z.val i ≠ 0 → i ≤ j) :
      (∀ x, 0 ≤ weights z x) ∧
      (∀ x, x ∉ s j → weights z x = 0) ∧
      (∑ x ∈ s j, weights z x) = 1 ∧
      (∑ x ∈ s j, weights z x • x) =
        finiteOrderComplexMap I (fun i => ∑ x ∈ s i, w i x • x) z := by
    have hz := (finiteOrderComplex_space I z.val).mp z.property
    have hcoeff (i : I) : (∑ x ∈ s j, z.val i * w i x) = z.val i := by
      by_cases hi : z.val i = 0
      · simp only [hi, zero_mul, Finset.sum_const_zero]
      · have hsub : s i ⊆ s j := (horder i j).mp (hj i hi)
        have heq : ∑ x ∈ s j, w i x = 1 := by
          rw [← hwsum i]
          exact (Finset.sum_subset hsub (fun x _ hx => hwzero i x hx)).symm
        rw [← Finset.mul_sum, heq, mul_one]
    have hvector (i : I) : (∑ x ∈ s j, (z.val i * w i x) • x) =
        z.val i • ∑ x ∈ s i, w i x • x := by
      by_cases hi : z.val i = 0
      · simp only [hi, zero_mul, zero_smul, Finset.sum_const_zero]
      · have hsub : s i ⊆ s j := (horder i j).mp (hj i hi)
        rw [Finset.smul_sum]
        simp only [smul_smul]
        apply (Finset.sum_subset hsub _).symm
        intro x _ hx
        rw [hwzero i x hx, mul_zero, zero_smul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      change 0 ≤ (∑ i, z.val i • w i) x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hz.1 i) (hw i x))
    · intro x hx
      simp only [weights, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : z.val i = 0
      · rw [hi, zero_mul]
      · have hxi : x ∉ s i := fun h => hx ((horder i j).mp (hj i hi) h)
        rw [hwzero i x hxi, mul_zero]
    · simp only [weights, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      exact (Finset.sum_congr rfl (fun i _ => hcoeff i)).trans hz.2.1
    · simp only [weights, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => hvector i)
  intro z z' heq
  obtain ⟨j, _, hj⟩ := order_simplex_support_max z
  obtain ⟨j', _, hj'⟩ := order_simplex_support_max z'
  obtain ⟨hznonneg, hzzero, hzsum, hzval⟩ := hweights z j hj
  obtain ⟨hz'nonneg, hz'zero, hz'sum, hz'val⟩ := hweights z' j' hj'
  have heqweights : weights z = weights z' :=
    simplicialComplex_convex_weights_unique K (hs j) (hs j') (weights z) (weights z')
      (fun x _ => hznonneg x) (fun x _ => hz'nonneg x) hzsum hz'sum hzzero hz'zero
      (hzval.trans (heq.trans hz'val.symm))
  have hz := (finiteOrderComplex_space I z.val).mp z.property
  have hz' := (finiteOrderComplex_space I z'.val).mp z'.property
  have hcoeff := nonnegative_chain_weighted_sum_unique s w
    (fun i => K.nonempty_of_mem_faces (hs i)) horder hw hwpos Finset.univ z.val z'.val
    (fun i _ => hz.1 i) (fun i _ => hz'.1 i)
    (fun i _ j _ hi hj => hz.2.2 i j hi hj)
    (fun i _ j _ hi hj => hz'.2.2 i j hi hj) heqweights
  apply Subtype.ext
  funext i
  exact hcoeff i (Finset.mem_univ i)

noncomputable def geometricFlagHomeomorphRange
    (K : Geometry.SimplicialComplex Real E) (s : I → Finset E)
    (hs : ∀ i, s i ∈ K.faces)
    (horder : ∀ i j, i ≤ j ↔ s i ⊆ s j)
    (c : I → E)
    (hc : ∀ i, ∃ w : E → Real, (∀ x ∈ s i, 0 < w x) ∧
      (∑ x ∈ s i, w x) = 1 ∧ (∑ x ∈ s i, w x • x) = c i) :
    (finiteOrderComplex I).space ≃ₜ Set.range (finiteOrderComplexMap I c) := by
  classical
  choose w hw hwsum hwval using hc
  let w' (i : I) (x : E) := if x ∈ s i then w i x else 0
  have hnonneg (i : I) (x : E) : 0 ≤ w' i x := by
    dsimp [w']
    split_ifs with hx
    · exact (hw i x hx).le
    · exact le_refl _
  have hpos (i : I) (x : E) : 0 < w' i x ↔ x ∈ s i := by
    by_cases hx : x ∈ s i
    · simp only [w', if_pos hx, hx, iff_true]
      exact hw i x hx
    · simp only [w', if_neg hx, lt_self_iff_false, hx]
  have hsum (i : I) : ∑ x ∈ s i, w' i x = 1 :=
    (Finset.sum_congr rfl (fun x hx => if_pos hx)).trans (hwsum i)
  have hval : (fun i => ∑ x ∈ s i, w' i x • x) = c := by
    funext i
    exact (Finset.sum_congr rfl (fun x hx => by simp only [w', if_pos hx])).trans (hwval i)
  have hinj : Function.Injective (finiteOrderComplexMap I c) := by
    rw [← hval]
    exact finiteOrderComplexMap_injective_of_geometric_faces K s hs horder w' hnonneg hpos hsum
  letI : CompactSpace (finiteOrderComplex I).space :=
    isCompact_iff_compactSpace.mp finiteOrderComplex_space_isCompact
  let e := Equiv.ofInjective (finiteOrderComplexMap I c) hinj
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    ((finiteOrderComplexMap I c).continuous.subtype_mk _)

end PoincareConjecture.Proofs.M02.Topology
