import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphStripSide

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_joined_graph_strips_inside
    (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {X Y : Set ℝ} (hX : IsOpen X) (hY : IsOpen Y)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f X) (hg : ContDiffOn ℝ ∞ g Y)
    {a b c d ua wa ub wb uc wc ud wd rho : ℝ}
    (P : TransverseGraphCuts f a b ua wa ub wb)
    (Q : TransverseGraphCuts g c d uc wc ud wd)
    {p w : AnnulusCoordinates}
    (hbaseP : L (b, f b) = p) (hbaseQ : R (c, g c) = p)
    (hdirP : L (ub, wb) = w) (hdirQ : R (uc, wc) = w)
    {U : Set AnnulusCoordinates} (hU : IsOpen U) (hrho : 0 < rho) :
    let S := P.linearCoordinates L hX hf
    let T := Q.linearCoordinates R hY hg
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < rho →
      (t, z) ∈ S.source ∧ (S (t, z) ∈ frontier U ↔ z = 0)) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < rho →
      (t, z) ∈ T.source ∧ (T (t, z) ∈ frontier U ↔ z = 0)) →
    (∀ᶠ r in 𝓝[>] (0 : ℝ), L (a, f a) + r • L (ua, wa) ∈ U) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) (rho / 2),
      (t, z) ∈ S.source ∧ S (t, z) ∈ closure U ∧ (0 < z → S (t, z) ∈ U)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) (rho / 2),
      (t, z) ∈ T.source ∧ T (t, z) ∈ closure U ∧ (0 < z → T (t, z) ∈ U) := by
  intro S T hstripS hstripT hray
  obtain ⟨z, hz, hp⟩ := m64Intrinsic_graph_strip_inward_endpoint_point
    L hX hf P hrho false hray
  have hinsideS := m64Intrinsic_closed_half_strip_inside hU S hrho hstripS
    ⟨0, by simp, z, hz, hp⟩
  obtain ⟨epsilonP, heP, hcutP⟩ :=
    P.right.exists_small_positive_parameters (lt_min (half_pos hrho) P.radius_pos)
  obtain ⟨epsilonQ, heQ, hcutQ⟩ :=
    Q.left.exists_small_positive_parameters (lt_min hrho Q.radius_pos)
  let r := min epsilonP epsilonQ / 2
  have hr : 0 < r := half_pos (lt_min heP heQ)
  have hrmin : r < min epsilonP epsilonQ := half_lt_self (lt_min heP heQ)
  have hP := hcutP r ⟨hr, hrmin.trans_le (min_le_left _ _)⟩
  have hQ := hcutQ r ⟨hr, hrmin.trans_le (min_le_right _ _)⟩
  have hzP : P.right.parameter r ∈ Icc (0 : ℝ) (rho / 2) :=
    ⟨hP.2.1.le, (hP.2.2.trans_le (min_le_left _ _)).le⟩
  have hzPr : P.right.parameter r ∈ Ioo (-P.radius) P.radius :=
    ⟨by linarith [hP.2.1, P.radius_pos], hP.2.2.trans_le (min_le_right _ _)⟩
  have hzQ : Q.left.parameter r ∈ Ioo (0 : ℝ) rho :=
    ⟨hQ.2.1, hQ.2.2.trans_le (min_le_left _ _)⟩
  have hzQr : Q.left.parameter r ∈ Ioo (-Q.radius) Q.radius :=
    ⟨by linarith [hQ.2.1, Q.radius_pos], hQ.2.2.trans_le (min_le_right _ _)⟩
  have hpU : p + r • w ∈ U := by
    have hp := (hinsideS 1 (by simp) (P.right.parameter r) hzP).2.2 hP.2.1
    change P.linearCoordinates L hX hf (1, P.right.parameter r) ∈ U at hp
    rwa [P.linearCoordinates_right L hX hf hzPr, P.right.parameter.left_inv hP.1,
      hbaseP, hdirP] at hp
  have hpointT : T (0, Q.left.parameter r) ∈ U := by
    change Q.linearCoordinates R hY hg (0, Q.left.parameter r) ∈ U
    rw [Q.linearCoordinates_left R hY hg hzQr, Q.left.parameter.left_inv hQ.1,
      hbaseQ, hdirQ]
    exact hpU
  exact ⟨hinsideS, m64Intrinsic_closed_half_strip_inside hU T hrho hstripT
    ⟨0, by simp, Q.left.parameter r, hzQ, hpointT⟩⟩

end PoincareConjecture
