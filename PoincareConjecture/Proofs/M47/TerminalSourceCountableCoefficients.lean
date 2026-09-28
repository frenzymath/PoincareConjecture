import PoincareConjecture.Proofs.M47.TerminalSourcePhysicalMaps
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.CanonicalDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSourceCountable_radial_smallness_mono
    {H K rho : ℝ} (hH : 0 ≤ H) (hHK : H ≤ K)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * rho →
      (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) ≤ 3) :
    ∀ s : ℝ, |s| ≤ 2 * rho →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3 := by
  intro s hs
  have hsq : H * s ^ 2 ≤ K * s ^ 2 :=
    mul_le_mul_of_nonneg_right hHK (sq_nonneg s)
  calc
    _ ≤ (K * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ ≤ (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (max_le_max_left 1 hsq))
        (mul_nonneg (hH.trans hHK) (sq_nonneg s))
    _ ≤ 3 := hsmall s hs

variable (U : ℕ → Opens E) [∀ i, Nonempty (U i)]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

theorem terminalSourceCountable_parametrization_smooth {i : ℕ}
    {e : U i → M} (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (ChartDistance.chartParametrization (fun j => (U j : Set E))
        (fun j => (U j).isOpen) e) (U i) := by
  apply ChartDistance.contMDiffOn_chartParametrization
  rw [canonicalDomain_chartedSpace_eq_opens]
  exact he

theorem terminalSourceCountable_parametrization_mfderiv {i : ℕ}
    {e : U i → M} (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) (x : U i) :
    mfderiv (𝓡 3) (𝓡 3)
      (ChartDistance.chartParametrization (fun j => (U j : Set E))
        (fun j => (U j).isOpen) e) x.val =
      mfderiv (𝓡 3) (𝓡 3) e x := by
  have hs : letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ e x := by
    rw [canonicalDomain_chartedSpace_eq_opens]
    exact he.contMDiffAt
  have hd := ChartDistance.mfderiv_chartParametrization
    (fun j => (U j : Set E)) (fun j => (U j).isOpen) x hs
  rw [canonicalDomain_chartedSpace_eq_opens] at hd
  exact hd

variable [IsManifold (𝓡 3) ∞ M]

theorem terminalSourceCountable_pullback_smooth (g : RiemannianMetric 3 M)
    {i : ℕ} {e : U i → M} (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) :
    ContDiffOn ℝ ∞
      (g.pullbackCoefficients
        (ChartDistance.chartParametrization (fun j => (U j : Set E))
          (fun j => (U j).isOpen) e)) (U i) := by
  intro x hx
  exact (g.contDiffAt_pullbackCoefficients
    ((terminalSourceCountable_parametrization_smooth U he).contMDiffAt
      ((U i).isOpen.mem_nhds hx))).contDiffWithinAt

variable {N : Type v} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold (𝓡 3) ∞ N]

theorem terminalSourceCountable_pullback_readout
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    {i : ℕ} {e : U i → M} (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (Phi : E → N) (hPhi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (U i))
    (hread : ∀ (x : U i) (v w : TangentSpace (𝓡 3) x),
      g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
        (mfderiv (𝓡 3) (𝓡 3) e x w) =
      h.inner (Phi x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U i => Phi y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U i => Phi y.val) x w)) :
    EqOn (g.pullbackCoefficients
      (ChartDistance.chartParametrization (fun j => (U j : Set E))
        (fun j => (U j).isOpen) e)) (h.pullbackCoefficients Phi) (U i) := by
  intro x hx
  let y : U i := ⟨x, hx⟩
  have hd := terminalSourceCountable_parametrization_mfderiv U he y
  have hrestrict := Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_restrict
    (I := 𝓡 3) (I' := 𝓡 3) (U i) Phi
    ((hPhi.contMDiffAt ((U i).isOpen.mem_nhds hx)).mdifferentiableAt (by simp))
    (x := y)
  ext v w
  change g.inner
    (ChartDistance.chartParametrization (fun j => (U j : Set E))
      (fun j => (U j).isOpen) e x)
    (mfderiv (𝓡 3) (𝓡 3)
      (ChartDistance.chartParametrization (fun j => (U j : Set E))
        (fun j => (U j).isOpen) e) x v)
    (mfderiv (𝓡 3) (𝓡 3)
      (ChartDistance.chartParametrization (fun j => (U j : Set E))
        (fun j => (U j).isOpen) e) x w) =
    h.inner (Phi x) (mfderiv (𝓡 3) (𝓡 3) Phi x v) (mfderiv (𝓡 3) (𝓡 3) Phi x w)
  rw [hd]
  have hpoint := ChartDistance.chartParametrization_apply
    (fun j => (U j : Set E)) (fun j => (U j).isOpen) e y
  rw [hpoint]
  have hr := hread y v w
  rw [hrestrict] at hr
  convert! hr using 1

omit [∀ i, Nonempty (U i)] in

theorem terminalSourceCountable_coefficient_jets {i : ℕ}
    {f g : E → E →L[ℝ] E →L[ℝ] ℝ} (heq : EqOn f g (U i))
    (m : ℕ) {x : E} (hx : x ∈ U i) :
    iteratedFDeriv ℝ m f x = iteratedFDeriv ℝ m g x := by
  have hgerm : f =ᶠ[𝓝 x] g := by
    filter_upwards [(U i).isOpen.mem_nhds hx] with y hy
    exact heq hy
  exact (hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds

end PoincareConjecture.M47
