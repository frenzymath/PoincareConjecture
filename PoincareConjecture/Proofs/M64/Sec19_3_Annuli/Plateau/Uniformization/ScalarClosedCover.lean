import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarInverseLipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

theorem scalarPotentialStrip_closure :
    closure scalarPotentialStrip = {y : Cover | y.1 ∈ Icc (0 : ℝ) 1} := by
  have hprod : scalarPotentialStrip = Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    ext y
    simp [scalarPotentialStrip]
  rw [hprod, closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_univ]
  ext y
  simp

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem exists_scalar_closed_cover_extension
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip) (htarget : e.target = scalarPotentialStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) :
    ∃ (K : ℝ≥0) (F : Cover → Plane),
      LipschitzWith K F ∧ EqOn F (scalarInverseCoverMap e) e.target ∧
      MapsTo F (closure e.target) (closure scalarAnnulus) ∧
      (∀ y ∈ closure e.target, H (F y) = y.1) ∧
      (∀ y ∈ closure e.target, F (y + (0, 1)) = F y) ∧
      (∀ t : ℝ, ‖F (0, t)‖ = 1) ∧ (∀ t : ℝ, ‖F (1, t)‖ = 2) := by
  obtain ⟨K, hK⟩ := scalarInverseCoverMap_lipschitzOn D hHc hHs hlap hinner houter
    hdV hP e hsource htarget he hes hei
  obtain ⟨F, hF, hFeq⟩ := hK.extend_finite_dimension
  have hFc := hF.continuous
  have hmaps : MapsTo F e.target scalarAnnulus := by
    intro y hy
    rw [← hFeq hy]
    exact scalarCoverMap_mem (hsource ▸ e.map_target hy)
  have hmapsclosed := hmaps.closure_of_continuousOn hFc.continuousOn
  have hpotential : ∀ y ∈ closure e.target, H (F y) = y.1 := by
    apply closure_minimal _ (isClosed_eq (hHc.comp hFc) continuous_fst)
    intro y hy
    change H (F y) = y.1
    rw [← hFeq hy]
    have h := congrArg Prod.fst (e.right_inv hy)
    rw [he] at h
    exact h
  have hperiod : ∀ y ∈ closure e.target, F (y + (0, 1)) = F y := by
    apply closure_minimal _
      (isClosed_eq (hFc.comp (continuous_id.add continuous_const)) hFc)
    intro y hy
    change F (y + (0, 1)) = F y
    have hy' : y + (0, 1) ∈ e.target := by
      rw [htarget] at hy ⊢
      simpa [scalarPotentialStrip] using hy
    rw [← hFeq hy', ← hFeq hy]
    exact scalarInverseCoverMap_periodic e hsource htarget hdeck hy
  have hzero (t : ℝ) : (0, t) ∈ closure e.target := by
    rw [htarget, scalarPotentialStrip_closure]
    norm_num
  have hone (t : ℝ) : (1, t) ∈ closure e.target := by
    rw [htarget, scalarPotentialStrip_closure]
    norm_num
  have hclosed : closure scalarAnnulus ⊆ {x : Plane | 0 ≤ scalarAnnulusDefining x} :=
    closure_minimal (fun x hx => ((scalarAnnulusDefining_pos x).mpr hx).le)
      (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  obtain ⟨c, hc, hsep⟩ :=
    annular_harmonic_linear_boundary_separation D hHc hHs hlap hinner houter
  refine ⟨_, F, hF, hFeq.symm, hmapsclosed, hpotential, hperiod, ?_, ?_⟩
  · intro t
    have hm := hclosed (hmapsclosed (hzero t))
    have hn := (scalarAnnulusDefining_nonneg _).mp hm
    have hs := (hsep _ hm).1
    rw [hpotential _ (hzero t)] at hs
    dsimp only at hs
    nlinarith
  · intro t
    have hm := hclosed (hmapsclosed (hone t))
    have hn := (scalarAnnulusDefining_nonneg _).mp hm
    have hs := (hsep _ hm).2
    rw [hpotential _ (hone t)] at hs
    dsimp only at hs
    nlinarith

end PoincareConjecture.M64Uniformization
