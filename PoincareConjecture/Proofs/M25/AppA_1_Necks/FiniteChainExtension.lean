import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainBarrier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedFrontierNeighbor












set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain




theorem exists_finite_forward_extension :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b →
      epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      ∀ (N' : EpsilonNeck g),
      N' ∈ C.source_necks →
      N'.epsilon = epsilon →
      N'.center ∈ closure ((C.neck b).region 0 epsilon⁻¹) →
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      ∃ (R : EpsilonNeck g) (D : BalancedNeckChain g epsilon),
        (R = N' ∨ R = N'.reverse) ∧
        R.SameUpToReversal N' ∧
        D.shape = ChainShape.finite a (b + 1) ∧
        D.source_necks = C.source_necks ∧
        D.neck = Function.update C.neck (b + 1) R := by
  classical
  obtain ⟨epsilonF, hF, hFcap, hbarrier⟩ :=
    exists_positive_frontier_negative_quarter_exclusion.{u}
  obtain ⟨epsilonP, hP, _, hpair⟩ := EpsilonNeck.exists_ordered_frontier_neighbor.{u}
  refine ⟨min epsilonF epsilonP, lt_min hF hP, (min_le_left _ _).trans hFcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape he hsep N' hsource hepsilon hy hyout
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  obtain ⟨i0, hi0⟩ := C.active_nonempty
  have hab : a ≤ b := ((hactive i0).mp hi0).1.trans ((hactive i0).mp hi0).2
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have hlast : (C.neck b).epsilon = epsilon := C.epsilon_eq b hb
  have hepos : 0 < epsilon := by rw [← hlast]; exact (C.neck b).epsilon_pos
  have hL : 0 < epsilon⁻¹ := inv_pos.mpr hepos
  have hyoutLast : N'.center ∉ (C.neck b).carrier := by
    intro hx
    exact hyout (mem_iUnion₂.mpr ⟨b, hb, hx⟩)
  obtain ⟨R, hchoice, hselected, _, hinter, hquarter, hoverlap, _, hbalance⟩ :=
    hpair (C.neck b) N' (by rw [hlast]; exact he.trans (min_le_right _ _))
      (hepsilon.trans hlast.symm) (hsep b hb) (by simpa only [hlast] using hy) hyoutLast
  have hRc : R.center = N'.center := hselected.2.2.1
  have hRu : R.carrier = N'.carrier := hselected.2.2.2.1
  have hRe : R.epsilon = epsilon := hselected.1.trans hepsilon
  have hexclusion := hbarrier C hshape (he.trans (min_le_left _ _)) hsep N'
    hepsilon hy hyout
  have hcenters {i : ℤ} (hi : i ∈ C.shape.active) : (C.neck i).center ≠ R.center := by
    intro h
    apply hyout
    apply mem_iUnion₂.mpr
    refine ⟨i, hi, ?_⟩
    rw [← hRc, ← h]
    exact (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere
  let V := Function.update C.neck (b + 1) R
  have hVnew : V (b + 1) = R := Function.update_self _ _ _
  have hVold {i : ℤ} (hi : i ∈ C.shape.active) : V i = C.neck i := by
    have hiI := (hactive i).mp hi
    have hile : i ≤ b := hiI.2
    have hine : i ≠ b + 1 := by omega
    exact Function.update_of_ne hine R C.neck
  have hold {i : ℤ} (hi : i ∈ Icc a (b + 1)) (hne : i ≠ b + 1) :
      i ∈ C.shape.active := by
    apply (hactive i).mpr
    rcases hi with ⟨hia, hib⟩
    exact ⟨hia, by omega⟩
  have holdPair {i : ℤ} (hi : i ∈ Icc a (b + 1)) (hi1 : i + 1 ∈ Icc a (b + 1))
      (hne : i ≠ b) : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active := by
    rcases hi with ⟨hia, hib⟩
    rcases hi1 with ⟨hi1a, hi1b⟩
    exact ⟨(hactive i).mpr ⟨hia, by omega⟩,
      (hactive (i + 1)).mpr ⟨hi1a, by omega⟩⟩
  let D : BalancedNeckChain g epsilon := {
    shape := .finite a (b + 1)
    neck := V
    source_necks := C.source_necks
    selected := by
      intro i hi
      change i ∈ Icc a (b + 1) at hi
      by_cases hin : i = b + 1
      · subst i
        exact ⟨N', hsource, hVnew ▸ hselected⟩
      · have hio := hold hi hin
        simpa only [hVold hio] using C.selected i hio
    active_nonempty := ⟨a, le_rfl, by omega⟩
    epsilon_eq := by
      intro i hi
      change i ∈ Icc a (b + 1) at hi
      by_cases hin : i = b + 1
      · subst i
        rw [hVnew]
        exact hRe
      · rw [hVold (hold hi hin)]
        exact C.epsilon_eq i (hold hi hin)
    centers_distinct := by
      intro i hi j hj hij
      change i ∈ Icc a (b + 1) at hi
      change j ∈ Icc a (b + 1) at hj
      by_cases hin : i = b + 1
      · subst i
        have hjo := hold hj (Ne.symm hij)
        rw [hVnew, hVold hjo]
        exact (hcenters hjo).symm
      · have hio := hold hi hin
        by_cases hjn : j = b + 1
        · subst j
          rw [hVold hio, hVnew]
          exact hcenters hio
        · have hjo := hold hj hjn
          rw [hVold hio, hVold hjo]
          exact C.centers_distinct hio hjo hij
    adjacent_overlap := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        exact hinter
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.adjacent_overlap i hio hi1o
    overlap_contains_quarters := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        simpa only [hlast] using hquarter
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.overlap_contains_quarters i hio hi1o
    overlap_within_three_quarters := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        simpa only [hlast] using hoverlap
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.overlap_within_three_quarters i hio hi1o
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change i ∈ Icc a (b + 1) at hi
      change j ∈ Icc a (b + 1) at hj
      have hio : i ∈ C.shape.active := by
        apply (hactive i).mpr
        rcases hi with ⟨hia, hib⟩
        rcases hj with ⟨hja, hjb⟩
        exact ⟨hia, by omega⟩
      by_cases hjn : j = b + 1
      · subst j
        refine ⟨-epsilon⁻¹ / 2, ⟨by linarith, by linarith⟩, ?_⟩
        rw [hVnew, hVold hio, hRu]
        exact hexclusion i hio
      · have hjo := hold hj hjn
        simpa only [hVold hio, hVold hjo] using
          C.later_disjoint_negative_end i hio j hjo hij
    balanced_center_distance := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        simpa only [hlast] using hbalance
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.balanced_center_distance i hio hi1o }
  exact ⟨R, D, hchoice, hselected, rfl, rfl, rfl⟩

end PoincareConjecture.BalancedNeckChain
