import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerSector

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_constrained_minimizer_no_corner
    (N : IntrinsicAnnulus) {K : Set AnnulusCoordinates}
    {γ : ℝ → AnnulusCoordinates} {L t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 L)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ τ : ℝ → AnnulusCoordinates, ContinuousOn τ (Icc 0 1) →
        τ 0 = γ a → τ 1 = γ b → MapsTo τ (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation N.metric τ 0 1)
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (h0 : (0 : AnnulusCoordinates) ∈ H.source)
    (hH : ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source)
    (v w : AnnulusCoordinates)
    (hv : N.metric.tangentNorm (H 0) (mfderiv (𝓡 2) (𝓡 2) H 0 v) = 1)
    (hw : N.metric.tangentNorm (H 0) (mfderiv (𝓡 2) (𝓡 2) H 0 w) = 1)
    (hsector : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates),
      (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ z = a • v + b • w) → H z ∈ K)
    {d : ℝ} (hd : 0 < d)
    (hlegs : ∀ r ∈ Ioo 0 d, γ (t₀ - r) = H (r • v) ∧ γ (t₀ + r) = H (r • w)) :
    mfderiv (𝓡 2) (𝓡 2) H 0 w = -mfderiv (𝓡 2) (𝓡 2) H 0 v := by
  by_contra hne
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hsector
  let F := H.restrOpen (Metric.ball (0 : AnnulusCoordinates) epsilon) Metric.isOpen_ball
  have hF0 : (0 : AnnulusCoordinates) ∈ F.source :=
    ⟨h0, Metric.mem_ball_self hepsilon⟩
  have hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source := hH.mono inter_subset_left
  obtain ⟨rho, hrho, hshort⟩ :=
    m64Intrinsic_exists_short_corner_sector_curve N F hF0 hF v w hv hw hne
  let r := min (rho / 2) (min (d / 2) (min (t₀ / 2) ((L - t₀) / 2)))
  have hr : 0 < r := lt_min (half_pos hrho)
    (lt_min (half_pos hd) (lt_min (half_pos ht₀.1) (half_pos (sub_pos.mpr ht₀.2))))
  have hrrho : r < rho := (min_le_left _ _).trans_lt (half_lt_self hrho)
  have hrd : r < d := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
    (half_lt_self hd)
  have hrt : r < t₀ := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_left _ _)).trans_lt (half_lt_self ht₀.1)
  have hrL : r < L - t₀ := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans_lt (half_lt_self (sub_pos.mpr ht₀.2))
  obtain ⟨σ, hσ, hσ0, hσ1, hσconf, hσlength⟩ := hshort r hr hrrho
  have hconf : MapsTo σ (Icc 0 1) K := by
    intro t ht
    obtain ⟨z, hz, heq⟩ := hσconf ht
    rw [← heq]
    exact hball hz.1.2 hz.2
  have hminσ := hmin (t₀ - r) ⟨by linarith, by linarith [ht₀.2]⟩
    (t₀ + r) ⟨by linarith [ht₀.1], by linarith⟩ (by linarith) σ hσ.continuousOn
      (hσ0.trans (hlegs r ⟨hr, hrd⟩).1.symm)
      (hσ1.trans (hlegs r ⟨hr, hrd⟩).2.symm) hconf
  have hdiff : (t₀ + r) - (t₀ - r) = 2 * r := by ring
  rw [hdiff] at hminσ
  exact (not_lt_of_ge hminσ) hσlength

end PoincareConjecture
