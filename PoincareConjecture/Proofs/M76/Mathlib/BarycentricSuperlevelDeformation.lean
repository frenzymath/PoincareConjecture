import PoincareConjecture.Proofs.M76.Mathlib.BarycentricMix
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic













set_option autoImplicit false

open Set unitInterval
open scoped BigOperators

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]




theorem sum_eq_one_of_mem_barycentricFace {s : Finset ι} {q : ι → ℝ}
    (hq : q ∈ barycentricFace s) : ∑ i ∈ s, q i = 1 := by
  classical
  rw [Fintype.sum_subset (fun i hi => by_contra fun hn => hi (hq.2 i hn))]
  exact hq.1.2

end StdSimplexCore

namespace PreAbstractSimplicialComplex

open StdSimplexCore

variable {ι : Type*} [Fintype ι]









theorem exists_barycentric_superlevel_deformation_preserving_faces_mass
    (A : PreAbstractSimplicialComplex ι) (s : Finset ι)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    let N : Set (ι → ℝ) := {q | q ∈ A.barycentricSpace ∧ c ≤ ∑ i ∈ s, q i}
    let D : Set (ι → ℝ) := A.barycentricSpace ∩ barycentricFace s
    IsCompact N ∧ D ⊆ N ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ D ⊆ U ∧ U ∩ A.barycentricSpace ⊆ N ∧
        ∃ H : C(I × N, (ι → ℝ)),
          (∀ z, H z ∈ N) ∧
          (∀ q : N, H (0, q) = (q : ι → ℝ)) ∧
          (∀ q : N, H (1, q) ∈ D) ∧
          (∀ (t : I) (q : N), (q : ι → ℝ) ∈ D → H (t, q) = (q : ι → ℝ)) ∧
          (∀ (t : I) (q : N) (u : Finset ι),
            (q : ι → ℝ) ∈ barycentricFace u → H (t, q) ∈ barycentricFace u) ∧
          ∀ (t : I) (q : N), (∑ i ∈ s, H (t, q) i) =
            (1 - (t : ℝ)) * (∑ i ∈ s, (q : ι → ℝ) i) + (t : ℝ) := by
  classical
  let N : Set (ι → ℝ) := {q | q ∈ A.barycentricSpace ∧ c ≤ ∑ i ∈ s, q i}
  let D : Set (ι → ℝ) := A.barycentricSpace ∩ barycentricFace s
  let m : (ι → ℝ) → ℝ := fun q => ∑ i ∈ s, q i
  have hmc : Continuous m := continuous_finsetSum s (fun i _ => continuous_apply i)
  have hm (q : N) : 0 < m q := hc.trans_le q.property.2
  have hr (q : N) : projectToFace s 0 q ∈ D := by
    obtain ⟨f, hf, hqf⟩ := mem_iUnion₂.mp q.property.1
    exact ⟨A.barycentricFace_subset_barycentricSpace hf
      (projectToFace_zero_mem_of_mem hqf (hm q)),
      projectToFace_zero_mem s hqf.1.1 (hm q)⟩
  have hDN : D ⊆ N := fun q hq => ⟨hq.1, by
    rw [sum_eq_one_of_mem_barycentricFace hq.2]
    exact hc1.le⟩
  let U : Set (ι → ℝ) := {q | c < m q}
  have hU : IsOpen U := isOpen_lt continuous_const hmc
  have hDU : D ⊆ U := by
    intro q hq
    change c < ∑ i ∈ s, q i
    rw [sum_eq_one_of_mem_barycentricFace hq.2]
    exact hc1
  have hUN : U ∩ A.barycentricSpace ⊆ N := fun _ hq => ⟨hq.2, hq.1.le⟩
  let H : I × N → (ι → ℝ) := fun z =>
    (1 - (z.1 : ℝ)) • (z.2 : ι → ℝ) + (z.1 : ℝ) • projectToFace s 0 z.2
  have hqc : Continuous (fun z : I × N => (z.2 : ι → ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have htc : Continuous (fun z : I × N => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hrc : Continuous (fun z : I × N => projectToFace s 0 z.2) :=
    (continuousOn_projectToFace_zero s).comp_continuous hqc (fun z => (hm z.2).ne')
  have hHc : Continuous H := ((continuous_const.sub htc).smul hqc).add (htc.smul hrc)
  have hHN (z : I × N) : H z ∈ N := by
    obtain ⟨f, hf, hqf⟩ := mem_iUnion₂.mp z.2.property.1
    refine ⟨A.barycentricFace_subset_barycentricSpace hf
      (convex_barycentricFace f hqf (projectToFace_zero_mem_of_mem hqf (hm z.2))
        (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)), ?_⟩
    have hsum : (∑ i ∈ s, H z i) = (1 - (z.1 : ℝ)) * m z.2 + (z.1 : ℝ) := by
      simp only [H, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, sum_eq_one_of_mem_barycentricFace (hr z.2).2, mul_one, m]
    rw [hsum]
    have hnonneg := mul_nonneg (sub_nonneg.mpr z.1.property.2)
      (sub_nonneg.mpr z.2.property.2)
    have hrest := mul_nonneg z.1.property.1 (sub_nonneg.mpr hc1.le)
    dsimp only [m] at hnonneg ⊢
    nlinarith
  refine ⟨A.isCompact_barycentricSpace.inter_right
    (isClosed_le continuous_const hmc), hDN, U, hU, hDU, hUN, ⟨H, hHc⟩, hHN,
      ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    change H (0, q) = (q : ι → ℝ)
    simp only [H, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
  · intro q
    change H (1, q) ∈ D
    simpa only [H, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add] using hr q
  · intro t q hq
    have hfix : projectToFace s 0 (q : ι → ℝ) = (q : ι → ℝ) :=
      projectToFace_eq_self s 0 q (sum_eq_one_of_mem_barycentricFace hq.2) hq.2.2 (by simp)
    change (1 - (t : ℝ)) • (q : ι → ℝ) + (t : ℝ) • projectToFace s 0 q = q
    rw [hfix, ← add_smul]
    simp
  · intro t q u hqu
    exact convex_barycentricFace u hqu (projectToFace_zero_mem_of_mem hqu (hm q))
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  · intro t q
    change (∑ i ∈ s, H (t, q) i) = _
    simp only [H, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_eq_one_of_mem_barycentricFace (hr q).2, mul_one]





theorem exists_barycentric_superlevel_deformation_preserving_faces
    (A : PreAbstractSimplicialComplex ι) (s : Finset ι)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    let N : Set (ι → ℝ) := {q | q ∈ A.barycentricSpace ∧ c ≤ ∑ i ∈ s, q i}
    let D : Set (ι → ℝ) := A.barycentricSpace ∩ barycentricFace s
    IsCompact N ∧ D ⊆ N ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ D ⊆ U ∧ U ∩ A.barycentricSpace ⊆ N ∧
        ∃ H : C(I × N, (ι → ℝ)),
          (∀ z, H z ∈ N) ∧
          (∀ q : N, H (0, q) = (q : ι → ℝ)) ∧
          (∀ q : N, H (1, q) ∈ D) ∧
          (∀ (t : I) (q : N), (q : ι → ℝ) ∈ D → H (t, q) = (q : ι → ℝ)) ∧
          ∀ (t : I) (q : N) (u : Finset ι),
            (q : ι → ℝ) ∈ barycentricFace u → H (t, q) ∈ barycentricFace u := by
  obtain ⟨hN, hDN, U, hU, hDU, hUN, H, hHN, hH0, hH1, hfix, hface, _⟩ :=
    A.exists_barycentric_superlevel_deformation_preserving_faces_mass s hc hc1
  exact ⟨hN, hDN, U, hU, hDU, hUN, H, hHN, hH0, hH1, hfix, hface⟩





theorem exists_barycentric_superlevel_deformation
    (A : PreAbstractSimplicialComplex ι) (s : Finset ι)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    let N : Set (ι → ℝ) := {q | q ∈ A.barycentricSpace ∧ c ≤ ∑ i ∈ s, q i}
    let D : Set (ι → ℝ) := A.barycentricSpace ∩ barycentricFace s
    IsCompact N ∧ D ⊆ N ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ D ⊆ U ∧ U ∩ A.barycentricSpace ⊆ N ∧
        ∃ H : C(I × N, (ι → ℝ)),
          (∀ z, H z ∈ N) ∧
          (∀ q : N, H (0, q) = (q : ι → ℝ)) ∧
          (∀ q : N, H (1, q) ∈ D) ∧
          ∀ (t : I) (q : N), (q : ι → ℝ) ∈ D → H (t, q) = (q : ι → ℝ) := by
  obtain ⟨hN, hDN, U, hU, hDU, hUN, H, hHN, hH0, hH1, hfix, _⟩ :=
    A.exists_barycentric_superlevel_deformation_preserving_faces s hc hc1
  exact ⟨hN, hDN, U, hU, hDU, hUN, H, hHN, hH0, hH1, hfix⟩

end PreAbstractSimplicialComplex
