import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Derivative

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem endpoint_value_sub_le_of_geodesic_hessian_le
    (D : LeviCivitaData g) {rho : M → ℝ} {U : Set M} {gamma : ℝ → M}
    {L H : ℝ} (hL : 0 ≤ L) (hU : IsOpen U)
    (hrho : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U)
    (hgamma : g.IsGeodesicOn gamma (Icc (0 : ℝ) L))
    (hgammaU : ∀ t ∈ Icc (0 : ℝ) L, gamma t ∈ U)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L,
      g.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1) = 1)
    (hhess : ∀ t ∈ Ioo (0 : ℝ) L,
      D.hessian rho (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1) ≤ H) :
    rho (gamma L) - rho (gamma 0) ≤
      L * mvfderiv (𝓡 n) rho (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) + H * L ^ 2 / 2 := by
  let F : ℝ → ℝ := rho ∘ gamma
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt F (deriv F t) t := by
    apply DifferentiableAt.hasDerivAt
    apply (contMDiffAt_iff_contDiffAt.mp
      (((hrho.contMDiffAt (hU.mem_nhds (hgammaU t ht))).of_le
        (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp t (hgamma.contMDiffAt ht))).differentiableAt
      (by simp)
  have hsecond (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) L) :
      HasDerivAt (deriv F)
        (D.hessian rho (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1)) t :=
    D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn hU hrho hgamma
      ⟨ht.1.le, ht.2.le⟩ (hgammaU t ⟨ht.1.le, ht.2.le⟩)
  have hquad := Poincare.Analysis.quadratic_upper_bound_of_hasDerivAt2_le
    (f := F) (f' := deriv F)
    (f'' := fun t => D.hessian rho (gamma t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1))
    hL hfirst hsecond hhess
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL⟩
  have hchain := congrArg (fun A => A (1 : ℝ))
    (mfderiv_comp 0
      ((hrho.contMDiffAt (hU.mem_nhds (hgammaU 0 hzero))).mdifferentiableAt (by simp))
      ((hgamma.contMDiffAt hzero).mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at hchain
  change deriv F 0 = mvfderiv (𝓡 n) rho (gamma 0)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) at hchain
  dsimp only [F, Function.comp_apply] at hquad hchain ⊢
  rw [hchain] at hquad
  linarith

end PoincareConjecture.LeviCivitaData
