import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Uniqueness








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem hasDerivAt_deriv_comp_geodesic_of_contMDiffOn
    (D : LeviCivitaData g) {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} {s : Set ℝ} (hγ : g.IsGeodesicOn γ s)
    {t : ℝ} (ht : t ∈ s) (htU : γ t ∈ U) :
    HasDerivAt (deriv (f ∘ γ))
      (D.hessian f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) t := by
  have hγt := hγ.contMDiffAt ht
  have hnearU : ∀ᶠ u in 𝓝 t, γ u ∈ U :=
    hγt.continuousAt.preimage_mem_nhds (hU.mem_nhds htU)
  obtain ⟨p, q, w, hlocal⟩ := hγ t ht
  let c := extChartAt (𝓡 n) p
  let F := f ∘ c.symm
  have hF (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ c.target)
      (hxU : c.symm x ∈ U) : ContDiffAt ℝ ∞ F x := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hf.contMDiffAt (hU.mem_nhds hxU)).comp x
      ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hx).contMDiffAt
        (extChartAt_target_mem_nhds' hx))
  have hfirst : ∀ᶠ u in 𝓝 t,
      HasDerivAt (f ∘ γ) (fderiv ℝ F (q u) (w u)) u := by
    filter_upwards [hlocal, hlocal.eventually_nhds, hnearU] with u hu hue huU
    have hquU : c.symm (q u) ∈ U := hu.1 ▸ huU
    have hd := ((hF (q u) hu.2.1 hquU).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt u hu.2.2.1
    apply hd.congr_of_eventuallyEq
    filter_upwards [hue] with v hv
    exact congrArg f hv.1
  have hqt := hlocal.self_of_nhds
  have hqtU : c.symm (q t) ∈ U := hqt.1 ▸ htU
  have hsecond := (((hF (q t) hqt.2.1 hqtU).fderiv_right (m := ∞)
    (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hqt.2.2.1
  have hfield := hsecond.clm_apply hqt.2.2.2
  have hH := D.hessian_in_chart p hqt.2.1
    (hf.contMDiffAt (hU.mem_nhds hqtU)) (w t) (w t)
  have hfieldH : HasDerivAt (deriv (f ∘ γ))
      (D.hessian f (c.symm (q t))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (w t))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (w t))) t := by
    rw [hH]
    have hd : HasDerivAt (fun u => fderiv ℝ F (q u) (w u))
        (fderiv ℝ (fderiv ℝ F) (q t) (w t) (w t) -
          fderiv ℝ F (q t)
            (CoordinateExponential.christoffelBilinear
              (g.pullbackCoefficients c.symm) (q t) (w t) (w t))) t := by
      simpa +instances only [Function.comp_def, map_neg, ← sub_eq_add_neg,
        CoordinateExponential.christoffelBilinear_apply] using hfield
    exact hd.congr_of_eventuallyEq (hfirst.mono fun _ hu => hu.deriv)
  have hcurve : γ =ᶠ[𝓝 t] fun u => c.symm (q u) := hlocal.mono fun _ hu => hu.1
  have hc := ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hqt.2.1).contMDiffAt
    (extChartAt_target_mem_nhds' hqt.2.1)).mdifferentiableAt (by simp)
  have hv := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp t hc hqt.2.2.1.differentiableAt.mdifferentiableAt)
  rw [mfderiv_eq_fderiv] at hv
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u => c.symm (q u)) t 1 =
    mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (deriv q t) at hv
  rw [hqt.2.2.1.deriv] at hv
  rw [hcurve.mfderiv_eq, hcurve.self_of_nhds, hv]
  exact hfieldH

end PoincareConjecture.LeviCivitaData
