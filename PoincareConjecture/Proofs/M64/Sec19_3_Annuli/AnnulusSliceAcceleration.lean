import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSliceDifferential
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CoordinateGaugeEquation
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M09 CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem m64Annulus_slice_acceleration_in_chart
    (D : LeviCivitaData g) (b : M) {f : LoopPlane → M}
    {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O)
    (hchart : MapsTo f O (extChartAt (𝓡 n) b).source)
    {ell : ℝ → LoopPlane} {J : Set ℝ} (hJ : IsOpen J)
    (hell : ContDiffOn ℝ ∞ ell J) (hmap : MapsTo ell J O)
    (d : LoopPlane) (hd : ∀ r ∈ J, HasDerivAt ell d r) {x : ℝ} (hx : x ∈ J) :
    let u := (extChartAt (𝓡 n) b) ∘ f
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    rampHorizontalCovariantDerivative D (f ∘ ell)
      (fun r => curveVelocity (f ∘ ell) r) x =
      chartVectorField b
        (covDerivAlong (christoffelBilinear B) u
          (fun q => fderiv ℝ u q d) d (ell x)) (f (ell x)) := by
  let c := extChartAt (𝓡 n) b
  let u := c ∘ f
  let B := g.pullbackCoefficients c.symm
  have he : extChartAt (𝓡 n) b =
      (chartAt (EuclideanSpace ℝ (Fin n)) b).toPartialEquiv := by
    ext y <;> simp
  have hu : ContDiffOn ℝ ∞ u O := by
    intro p hp
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (f p) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hchart hp)
    exact (contMDiffAt_iff_contDiffAt.mp
      (hc.comp p (hf.contMDiffAt (hO.mem_nhds hp)))).contDiffWithinAt
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 2 (f ∘ ell) J :=
    (hf.comp hell.contMDiffOn hmap).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgammaChart : MapsTo (f ∘ ell) J
      (chartAt (EuclideanSpace ℝ (Fin n)) b).source := by
    simpa only [he] using hchart.comp hmap
  have hacc := M63.pullback_velocity_eq_chart_acceleration D b hJ hgamma hgammaChart hx
  let z := fun r => u (ell r)
  have hz (r : ℝ) (hr : r ∈ J) : HasDerivAt z (fderiv ℝ u (ell r) d) r :=
    ((hu.contDiffAt (hO.mem_nhds (hmap hr))).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt r (hd r hr)
  have hz' : (deriv z) =ᶠ[𝓝 x] fun r => fderiv ℝ u (ell r) d := by
    filter_upwards [hJ.mem_nhds hx] with r hr
    exact (hz r hr).deriv
  have hdu : ContDiffAt ℝ ∞ (fun p => fderiv ℝ u p d) (ell x) :=
    ((hu.contDiffAt (hO.mem_nhds (hmap hx))).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const
  have hsecond : deriv (deriv z) x = fderiv ℝ (fun p => fderiv ℝ u p d) (ell x) d :=
    hz'.deriv_eq.trans (((hdu.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
      (hd x hx)).deriv)
  have hacc' : rampHorizontalCovariantDerivative D (f ∘ ell)
      (fun r => curveVelocity (f ∘ ell) r) x =
      chartVectorField b
        (deriv (deriv z) x + coordinateChristoffel B (u (ell x)) (deriv z x) (deriv z x))
        (f (ell x)) := by
    simpa only [c, u, B, z, he, Function.comp_def] using! hacc
  rw [hsecond, (hz x hx).deriv] at hacc'
  exact hacc'

end PoincareConjecture
