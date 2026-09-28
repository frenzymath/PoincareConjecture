import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointStripFrontier









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture




theorem m64Intrinsic_graph_strip_inward_endpoint_point
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {X : Set ℝ} (hX : IsOpen X) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f X)
    {a b ua wa ub wb rho : ℝ} (P : TransverseGraphCuts f a b ua wa ub wb)
    (hrho : 0 < rho) (right : Bool) {U : Set AnnulusCoordinates}
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      L (if right then (b, f b) else (a, f a)) +
        r • L (if right then (ub, wb) else (ua, wa)) ∈ U) :
    ∃ z ∈ Ioo (0 : ℝ) rho,
      P.linearCoordinates L hX hf (if right then 1 else 0, z) ∈ U := by
  cases right
  · obtain ⟨epsilon, hepsilon, hcut⟩ :=
      P.left.exists_small_positive_parameters (lt_min hrho P.radius_pos)
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) epsilon :=
      Ioo_mem_nhdsGT hepsilon
    obtain ⟨r, hr, hrU⟩ := (hsmall.and hray).exists
    have hrcut := hcut r hr
    have hz : P.left.parameter r ∈ Ioo (-P.radius) P.radius :=
      ⟨by linarith [hrcut.2.1, P.radius_pos], hrcut.2.2.trans_le (min_le_right _ _)⟩
    refine ⟨P.left.parameter r,
      ⟨hrcut.2.1, hrcut.2.2.trans_le (min_le_left _ _)⟩, ?_⟩
    simp only [Bool.false_eq_true, if_false]
    rw [P.linearCoordinates_left L hX hf hz, P.left.parameter.left_inv hrcut.1]
    exact hrU
  · obtain ⟨epsilon, hepsilon, hcut⟩ :=
      P.right.exists_small_positive_parameters (lt_min hrho P.radius_pos)
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) epsilon :=
      Ioo_mem_nhdsGT hepsilon
    obtain ⟨r, hr, hrU⟩ := (hsmall.and hray).exists
    have hrcut := hcut r hr
    have hz : P.right.parameter r ∈ Ioo (-P.radius) P.radius :=
      ⟨by linarith [hrcut.2.1, P.radius_pos], hrcut.2.2.trans_le (min_le_right _ _)⟩
    refine ⟨P.right.parameter r,
      ⟨hrcut.2.1, hrcut.2.2.trans_le (min_le_left _ _)⟩, ?_⟩
    simp only [if_true]
    rw [P.linearCoordinates_right L hX hf hz, P.right.parameter.left_inv hrcut.1]
    exact hrU




theorem m64Intrinsic_closed_half_strip_inside
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (S : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {rho : ℝ} (hrho : 0 < rho)
    (hstrip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < rho →
      (t, z) ∈ S.source ∧ (S (t, z) ∈ frontier U ↔ z = 0))
    (hpoint : ∃ t ∈ Icc (0 : ℝ) 1, ∃ z ∈ Ioo (0 : ℝ) rho, S (t, z) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) (rho / 2),
      (t, z) ∈ S.source ∧ S (t, z) ∈ closure U ∧ (0 < z → S (t, z) ∈ U) := by
  let Q := Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) rho
  have hQ : Q ⊆ S.source := fun q hq =>
    (hstrip q.1 hq.1 q.2 (by simpa only [abs_of_pos hq.2.1] using hq.2.2)).1
  have hconn : IsPreconnected (S '' Q) :=
    (isPreconnected_Icc.prod isPreconnected_Ioo).image S (S.continuousOn.mono hQ)
  obtain ⟨t, ht, z, hz, hp⟩ := hpoint
  have hsub : S '' Q ⊆ U := hconn.subset_of_closure_inter_subset hU
    ⟨S (t, z), ⟨(t, z), ⟨ht, hz⟩, rfl⟩, hp⟩ (by
      rintro p ⟨hp, q, hq, rfl⟩
      by_contra hn
      have hpf : S q ∈ frontier U := ⟨hp, by simpa only [hU.interior_eq] using hn⟩
      exact hq.2.1.ne' ((hstrip q.1 hq.1 q.2
        (by simpa only [abs_of_pos hq.2.1] using hq.2.2)).2.mp hpf))
  intro t ht z hz
  have hzr : z < rho := hz.2.trans_lt (half_lt_self hrho)
  have hzabs : |z| < rho := by simpa only [abs_of_nonneg hz.1] using hzr
  have hpos : 0 < z → S (t, z) ∈ U := fun hp => hsub ⟨(t, z), ⟨ht, hp, hzr⟩, rfl⟩
  refine ⟨(hstrip t ht z hzabs).1, ?_, hpos⟩
  rcases hz.1.eq_or_lt with hz0 | hp
  · exact frontier_subset_closure ((hstrip t ht z hzabs).2.mpr hz0.symm)
  · exact subset_closure (hpos hp)

end PoincareConjecture
