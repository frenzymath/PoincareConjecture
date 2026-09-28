import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import Mathlib.Topology.Compactness.Compact










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} {Z : Type w} [TopologicalSpace Z] [CompactSpace Z]
  {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem exists_compact_c2_family_of_local_families
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M))
    (gamma : Z → ℝ → M) (e : M → W)
    (hlocal : ∀ z0 : Z, ∃ N : Set Z, IsClosed N ∧ z0 ∈ interior N ∧
      ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : N → ℝ → ℝ → M,
        (∀ z, M63C2ShrinkingCurveOn F (c z) (Icc a T)) ∧
        (∀ z x, c z x a = gamma z x) ∧
        Continuous (fun z : (N × ℝ) × Icc a T => e (c z.1.1 z.1.2 z.2)) ∧
        Continuous (fun z : (N × ℝ) × Icc a T =>
          deriv (fun x => e (c z.1.1 x z.2)) z.1.2) ∧
        Continuous (fun z : (N × ℝ) × Icc a T =>
          deriv (deriv (fun x => e (c z.1.1 x z.2))) z.1.2)) :
    ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : Z → ℝ → ℝ → M,
      (∀ z, M63C2ShrinkingCurveOn F (c z) (Icc a T)) ∧
      (∀ z x, c z x a = gamma z x) ∧
      Continuous (fun z : (Z × ℝ) × Icc a T => e (c z.1.1 z.1.2 z.2)) ∧
      Continuous (fun z : (Z × ℝ) × Icc a T =>
        deriv (fun x => e (c z.1.1 x z.2)) z.1.2) ∧
      Continuous (fun z : (Z × ℝ) × Icc a T =>
        deriv (deriv (fun x => e (c z.1.1 x z.2))) z.1.2) := by
  classical
  choose N _hNclosed hN tau htau _htaub d hd hd0 hzero hfirst hsecond using hlocal
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun i : Z => interior (N i)) (fun _ => isOpen_interior)
    (fun z _ => mem_iUnion.mpr ⟨z, hN z⟩)
  have hcover (z : Z) : ∃ i, i ∈ I ∧ z ∈ interior (N i) := by
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp (hI (mem_univ z))
    exact ⟨i, hi, hz⟩
  have htime : ∀ s : Finset Z, ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∀ i ∈ s, T ≤ tau i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨b, hab, le_rfl, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨T, haT, hTb, hTi⟩ := ih
      refine ⟨min T (tau i), lt_min haT (htau i), (min_le_left _ _).trans hTb, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hTi j hj)
  obtain ⟨T, haT, hTb, hTi⟩ := htime I
  choose select hselect hmember using hcover
  let c : Z → ℝ → ℝ → M := fun z => d (select z) ⟨z, interior_subset (hmember z)⟩
  have hrestrict (i : Z) (hi : i ∈ I) (z : N i) :
      M63C2ShrinkingCurveOn F (d i z) (Icc a T) :=
    c2_restrict (hd i z) (Icc_subset_Icc_right (hTi i hi))
  have hc (z : Z) : M63C2ShrinkingCurveOn F (c z) (Icc a T) :=
    hrestrict (select z) (hselect z) ⟨z, interior_subset (hmember z)⟩
  have hc0 (z : Z) (x : ℝ) : c z x a = gamma z x :=
    hd0 (select z) ⟨z, interior_subset (hmember z)⟩ x
  have hmatch (i : Z) (hi : i ∈ I) (z : N i) :
      ∀ t ∈ Icc a T, ∀ x, c z x t = d i z x t :=
    c2ShrinkingCurve_unique_closed F hcompact (hc z) (hrestrict i hi z)
      (fun x => (hc0 z x).trans (hd0 i z x).symm)
  let D : I → Set ((Z × ℝ) × Icc a T) := fun i => {p | p.1.1 ∈ N i.1}
  have hDcover (p : (Z × ℝ) × Icc a T) : ∃ i : I, D i ∈ 𝓝 p := by
    let i := select p.1.1
    have hi : i ∈ I := hselect p.1.1
    have hz : p.1.1 ∈ interior (N i) := hmember p.1.1
    have hopen : IsOpen {q : (Z × ℝ) × Icc a T | q.1.1 ∈ interior (N i)} :=
      isOpen_interior.preimage (continuous_fst.fst)
    refine ⟨⟨i, hi⟩, mem_of_superset (hopen.mem_nhds hz) ?_⟩
    intro q hq
    change q.1.1 ∈ N i
    exact interior_subset hq
  have hcontinuous (A : (ℝ → M) → ℝ → W)
      (hA : ∀ i, Continuous (fun p : (N i × ℝ) × Icc a (tau i) =>
        A (fun x => d i p.1.1 x p.2) p.1.2)) :
      Continuous (fun p : (Z × ℝ) × Icc a T => A (fun x => c p.1.1 x p.2) p.1.2) := by
    apply continuous_of_cover_nhds hDcover
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    let inclusion : D i → (N i.1 × ℝ) × Icc a (tau i.1) := fun p =>
      ((⟨p.1.1.1, p.2⟩, p.1.1.2),
        ⟨p.1.2, p.1.2.2.1, p.1.2.2.2.trans (hTi i.1 i.2)⟩)
    have hinclusion : Continuous inclusion := by
      fun_prop
    apply ((hA i.1).comp hinclusion).congr
    intro p
    change A (fun x => d i.1 ⟨p.1.1.1, p.2⟩ x p.1.2) p.1.1.2 =
      A (fun x => c p.1.1.1 x p.1.2) p.1.1.2
    exact congrArg (fun f : ℝ → M => A f p.1.1.2)
      (funext (fun x => (hmatch i.1 i.2 ⟨p.1.1.1, p.2⟩ p.1.2 p.1.2.2 x).symm))
  exact ⟨T, haT, hTb, c, hc, hc0,
    hcontinuous (fun f x => e (f x)) hzero,
    hcontinuous (fun f x => deriv (fun y => e (f y)) x) hfirst,
    hcontinuous (fun f x => deriv (deriv (fun y => e (f y))) x) hsecond⟩

end PoincareConjecture.M63
