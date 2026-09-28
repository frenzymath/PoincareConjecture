import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCornerCaps
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapUnionSeparators

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_disjoint_finite_corner_caps
    {J : Type*} [Finite J] (alpha beta : J → ℝ → AnnulusCoordinates)
    (A B : J → ℝ) (K : J → Set AnnulusCoordinates)
    (ha : ∀ j, ContDiff ℝ ∞ (alpha j)) (hb : ∀ j, ContDiff ℝ ∞ (beta j))
    (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (hai : ∀ j, InjOn (alpha j) (Icc 0 (A j)))
    (hbi : ∀ j, InjOn (beta j) (Icc 0 (B j)))
    (hbase : ∀ j, beta j 0 = alpha j 0)
    (hind : ∀ j, LinearIndependent ℝ
      (![deriv (alpha j) 0, deriv (beta j) 0] : Fin 2 → AnnulusCoordinates))
    (hK : ∀ j, IsCompact (K j)) (hpK : ∀ j, alpha j 0 ∉ K j)
    (hdistinct : Function.Injective (fun j => alpha j 0))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : ∀ j, frontier U = alpha j '' Icc 0 (A j) ∪ beta j '' Icc 0 (B j) ∪ K j)
    (hfV : frontier V = frontier U) :
    ∃ (H : J → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : J → ℝ)
      (F : J → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : J → Set AnnulusCoordinates) (positive : J → Bool),
      let C (j : J) (i : Bool × Bool) :=
        F j i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r j}
      let D (j : J) := ⋃ i,
        ⋃ (_ : if positive j then i = (true, true) else i ≠ (true, true)), C j i
      (∀ j,
        0 < r j ∧ r j ≤ min (A j) (B j) / 3 ∧ (0 : ℝ × ℝ) ∈ (H j).source ∧
        H j 0 = alpha j 0 ∧
        ContDiffOn ℝ ∞ (H j) (H j).source ∧ ContDiffOn ℝ ∞ (H j).symm (H j).target ∧
        (∀ s : ℝ, H j (s, 0) = alpha j s) ∧ (∀ s : ℝ, H j (0, s) = beta j s) ∧
        (∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) (r j),
          sectorParameterEquiv 0 i (s, 0) ∈ (H j).source ∧
          sectorParameterEquiv 0 i (0, s) ∈ (H j).source) ∧
        (∀ q ∈ (H j).source, H j q ∈ frontier U ↔
          (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)) ∧
        (∀ q ∈ (H j).source, H j q ∈ closure U ↔
          if positive j then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0) ∧
        (∀ i,
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r j} ⊆ (F j i).source ∧
          (F j i).target ⊆ (H j).target ∧
          ContDiffOn ℝ ∞ (F j i) (F j i).source ∧
          ContDiffOn ℝ ∞ (F j i).symm (F j i).target ∧
          (∀ s ∈ Icc (0 : ℝ) (r j), F j i (s, 0) = H j (sectorParameterEquiv 0 i (s, 0))) ∧
          (∀ s ∈ Icc (0 : ℝ) (r j), F j i (0, s) = H j (sectorParameterEquiv 0 i (0, s))) ∧
          (∀ t : ℝ, F j i ((1 - t) * r j, t * r j) =
            (1 - t) • F j i (r j, 0) + t • F j i (0, r j)) ∧
          C j i ⊆ H j '' ((H j).source ∩ (sectorParameterEquiv 0 i) ''
            {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
          C j i ∩ H j '' ((H j).source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
            H j '' ((sectorParameterEquiv 0 i) ''
              ((Icc (0 : ℝ) (r j) ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) (r j))))) ∧
        IsOpen (W j) ∧ alpha j 0 ∈ W j ∧
        IsCompact (D j) ∧ D j ⊆ closure U ∧ W j ∩ closure U ⊆ D j ∧
        D j ∩ frontier U = alpha j '' Icc 0 (r j) ∪ beta j '' Icc 0 (r j)) ∧
      Pairwise (fun j k => Disjoint (D j) (D k)) := by
  classical
  obtain ⟨O, hO, hOO⟩ := (finite_range (fun j => alpha j 0)).t2_separation
  have hcorner (j : J) := m64Intrinsic_exists_two_arc_corner_caps
    (ha j) (hb j) (hA j) (hB j) (hai j) (hbi j) (hbase j) (hind j)
    (hK j) (hpK j) hU hV hdisj (hfU j) hfV (hO (alpha j 0)).2 (hO (alpha j 0)).1
  choose H r F W positive hdata using hcorner
  let C (j : J) (i : Bool × Bool) :=
    F j i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r j}
  let D (j : J) := ⋃ i,
    ⋃ (_ : if positive j then i = (true, true) else i ≠ (true, true)), C j i
  have hDO (j : J) : D j ⊆ O (alpha j 0) :=
    (hdata j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨H, r, F, W, positive, ?_, ?_⟩
  · intro j
    obtain ⟨hr, hrbound, hzero, hbaseH, _, hH, hHi, haxis, haxis', hsmall,
      hfrontier, hside, hF, hW, hpW, _, hsub, hcover, hcontact⟩ := hdata j
    have hcompact : IsCompact (D j) := by
      apply isCompact_iUnion
      intro i
      apply isCompact_iUnion
      intro _
      exact m64Intrinsic_cap_isCompact (F j i) (hF i).1
    exact ⟨hr, hrbound, hzero, hbaseH, hH, hHi, haxis, haxis', hsmall,
      hfrontier, hside, hF, hW, hpW, hcompact, hsub, hcover, hcontact⟩
  · intro j k hjk
    exact (hOO (mem_range_self j) (mem_range_self k)
      (fun h => hjk (hdistinct h))).mono (hDO j) (hDO k)

end PoincareConjecture
