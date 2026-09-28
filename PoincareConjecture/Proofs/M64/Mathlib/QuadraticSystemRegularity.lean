import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomiRegularity
import Mathlib.Analysis.Calculus.ContDiff.WithLp












set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture

open EuclideanTranslationNative





theorem m64QuadraticSystem_contDiffOn {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → LoopPlane → ℝ)
    (v : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {S : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) S)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C B H β : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hv : ContinuousOn v U)
    (huv : ∀ j, (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U] fun z => v z j)
    (hholder : ∀ x ∈ U, ∀ z ∈ U, ∀ j, |v z j - v x j| ≤ H * ‖z - x‖ ^ β)
    (hdecay : ∀ p ∈ U, ∃ Λ ≥ 0, ∃ R > 0,
      ∀ x ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R →
        (∫ z in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) ≤
          Λ * r ^ (2 * β)) :
    ContDiffOn ℝ 1 v U := by
  intro p hp
  obtain ⟨Λ, hΛ, R, hR, henergy⟩ := hdecay p hp
  have hcoord := M65Boundary.quadratic_holder_contDiffAt u d f
    (fun j z => v z j) hf hU hfs hweak heq hC hH hβ hΛ hR hgrowth hbound
    (fun j => (EuclideanSpace.proj j).continuous.comp_continuousOn hv)
    huv hholder hp henergy
  exact ((contDiffAt_piLp 2).mpr hcoord).contDiffWithinAt

end PoincareConjecture
