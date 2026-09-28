import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.NeckChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem axialCoordinate_contMDiffOn (N : EpsilonNeck g) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (axialCoordinate N) N.carrier := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  intro x hx
  have hi := N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)
  have hsnd : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : UnitTwoSphere × ℝ => z.2) (N.coordinate_inverse x) :=
    contMDiffAt_snd
  change ContMDiffWithinAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
    (fun y => (N.coordinate_inverse y).2) N.carrier x
  simpa [axialCoordinate, Function.comp_def] using
    (hsnd.comp _ hi).contMDiffWithinAt

theorem hasDerivAt_axialCoordinate_comp_geodesic
    (N : EpsilonNeck g) {γ : ℝ → M} {L : ℝ}
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hγN : ∀ t ∈ Icc 0 L, γ t ∈ N.carrier)
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    HasDerivAt (axialCoordinate N ∘ γ)
      (mvfderiv (𝓡 3) (axialCoordinate N) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) t := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let F : ℝ → ℝ := axialCoordinate N ∘ γ
  have hfirst (t : ℝ) (ht : t ∈ Icc 0 L) :
      HasDerivAt F (deriv F t) t := by
    have hf := (N.axialCoordinate_contMDiffOn.contMDiffAt
      (N.carrier_open.mem_nhds (hγN t ht))).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)
    apply DifferentiableAt.hasDerivAt
    apply (contMDiffAt_iff_contDiffAt.mp
      (hf.comp t (hγ.contMDiffAt ht))).differentiableAt
      (by simp)
  have hdu : deriv F t =
      mvfderiv (𝓡 3) (axialCoordinate N) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) := by
    have heq := congrArg (fun L => L (1 : ℝ))
      (mfderiv_comp t
        (((N.axialCoordinate_contMDiffOn).contMDiffAt
          (N.carrier_open.mem_nhds (hγN t ht))).mdifferentiableAt
          (by simp))
        ((hγ.contMDiffAt ht).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change deriv F t =
      mvfderiv (𝓡 3) (axialCoordinate N) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) at heq
    exact heq
  have hfirst_t := hfirst t ht
  rw [hdu] at hfirst_t
  exact hfirst_t

theorem hasDerivAt_deriv_axialCoordinate_comp_geodesic
    (D : LeviCivitaData g) (N : EpsilonNeck g) {γ : ℝ → M} {L : ℝ}
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hγN : ∀ t ∈ Icc 0 L, γ t ∈ N.carrier)
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    HasDerivAt (deriv (axialCoordinate N ∘ γ))
      (D.hessian (axialCoordinate N) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) t := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  exact D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn
    N.carrier_open N.axialCoordinate_contMDiffOn hγ ht (hγN t ht)

end PoincareConjecture.EpsilonNeck
