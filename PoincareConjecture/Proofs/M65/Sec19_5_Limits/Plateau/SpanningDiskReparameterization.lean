import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.DensityChange
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65SpanningDisk_reparameterize {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ)
    (φ ψ : LoopPlane → LoopPlane)
    (hφ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 φ z)
    (hψ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 ψ z)
    (hφdisk : MapsTo φ loopDiskSet loopDiskSet)
    (hψdisk : MapsTo ψ loopDiskSet loopDiskSet)
    (hφcircle : ∀ z, ‖z‖ = 1 → ‖φ z‖ = 1)
    (hψcircle : ∀ z, ‖z‖ = 1 → ‖ψ z‖ = 1)
    (hleft : ∀ z ∈ loopDiskSet, ψ (φ z) = z)
    (hright : ∀ z ∈ loopDiskSet, φ (ψ z) = z) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.map = D.map ∘ φ ∧ D'.area = D.area ∧
      ∀ z : LoopCircle, D'.reparameterization.map z =
        D.reparameterization.map ⟨φ z, hφcircle z z.property⟩ := by
  have hs : MeasurableSet loopDiskSet := isClosed_closedBall.measurableSet
  have hinj : InjOn φ loopDiskSet := by
    intro x hx y hy hxy
    calc
      x = ψ (φ x) := (hleft x hx).symm
      _ = ψ (φ y) := congrArg ψ hxy
      _ = y := hleft y hy
  have himage : φ '' loopDiskSet = loopDiskSet := by
    apply Subset.antisymm hφdisk.image_subset
    intro z hz
    exact ⟨ψ z, hψdisk hz, hright z hz⟩
  have hDpull : ∀ᵐ z ∂volume, z ∈ loopDiskSet →
      MDifferentiableAt (𝓡 2) (𝓡 3) D.map (φ z) := by
    let N := {y | y ∈ loopDiskSet ∧ ¬MDifferentiableAt (𝓡 2) (𝓡 3) D.map y}
    have hN : volume N = 0 := by
      simpa only [Classical.not_imp, N] using ae_iff.mp D.ae_manifold_differentiable
    have hnull : volume (ψ '' N) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (fun y hy => (hψ y hy.1).differentiableAt one_ne_zero |>.differentiableWithinAt) hN
    apply ae_iff.mpr
    apply measure_mono_null _ hnull
    intro z hz
    have hz' : z ∈ loopDiskSet ∧ ¬MDifferentiableAt (𝓡 2) (𝓡 3) D.map (φ z) := by
      exact Classical.not_imp.mp hz
    exact ⟨φ z, ⟨hφdisk hz'.1, hz'.2⟩, hleft z hz'.1⟩
  have hdensity : parametrizedAreaDensity g (D.map ∘ φ) =ᵐ[volume.restrict loopDiskSet]
      fun z => |(fderiv ℝ φ z).det| • parametrizedAreaDensity g D.map (φ z) := by
    filter_upwards [(ae_restrict_iff' hs).mpr hDpull, ae_restrict_mem hs] with z hDz hz
    exact m65ParametrizedAreaDensity_comp g D.map φ z hDz
      ((hφ z hz).differentiableAt one_ne_zero)
  have hderiv : ∀ z ∈ loopDiskSet,
      HasFDerivWithinAt φ (fderiv ℝ φ z) loopDiskSet z :=
    fun z hz => ((hφ z hz).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have hweighted : IntegrableOn
      (fun z => |(fderiv ℝ φ z).det| • parametrizedAreaDensity g D.map (φ z))
      loopDiskSet volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hderiv hinj _).mp
    rw [himage]
    exact D.area_integrable
  have harea : parametrizedRiemannianArea g (D.map ∘ φ) = D.area := by
    calc
      _ = ∫ z in loopDiskSet,
          |(fderiv ℝ φ z).det| • parametrizedAreaDensity g D.map (φ z) :=
        integral_congr_ae hdensity
      _ = ∫ z in φ '' loopDiskSet, parametrizedAreaDensity g D.map z :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv hinj _).symm
      _ = D.area := by rw [himage]; rfl
  have hφon : ContDiffOn ℝ 1 φ loopDiskSet := fun z hz => (hφ z hz).contDiffWithinAt
  obtain ⟨K, hK⟩ := hφon.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 1)
    (isCompact_closedBall 0 1)
  have hcircle_mem (z : LoopCircle) : z.1 ∈ loopDiskSet :=
    mem_closedBall_zero_iff.mpr z.property.le
  let R : CircleReparameterization := {
    map := fun z => ⟨φ z, hφcircle z z.property⟩
    inverse := fun z => ⟨ψ z, hψcircle z z.property⟩
    left_inverse := fun z => Subtype.ext (hleft z (hcircle_mem z))
    right_inverse := fun z => Subtype.ext (hright z (hcircle_mem z))
    continuous_map := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ((hφ z (hcircle_mem z)).continuousAt.comp continuousAt_subtype_val)
    continuous_inverse := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ((hψ z (hcircle_mem z)).continuousAt.comp continuousAt_subtype_val) }
  let D' : LipschitzSpanningDisk g γ := {
    map := D.map ∘ φ
    continuous_on_disk := D.continuous_on_disk.comp hφon.continuousOn hφdisk
    ae_manifold_differentiable := by
      filter_upwards [hDpull] with z hz hzdisk
      exact (hz hzdisk).comp z ((hφ z hzdisk).differentiableAt one_ne_zero).mdifferentiableAt
    reparameterization := {
      map := D.reparameterization.map ∘ R.map
      inverse := R.inverse ∘ D.reparameterization.inverse
      left_inverse := by
        intro z
        exact (congrArg R.inverse (D.reparameterization.left_inverse (R.map z))).trans
          (R.left_inverse z)
      right_inverse := by
        intro z
        exact (congrArg D.reparameterization.map
          (R.right_inverse (D.reparameterization.inverse z))).trans
          (D.reparameterization.right_inverse z)
      continuous_map := D.reparameterization.continuous_map.comp R.continuous_map
      continuous_inverse := R.continuous_inverse.comp D.reparameterization.continuous_inverse }
    boundary_eq := fun z => D.boundary_eq (R.map z)
    lipschitz_constant := D.lipschitz_constant * K
    lipschitz_nonnegative := mul_nonneg D.lipschitz_nonnegative K.coe_nonneg
    lipschitz_on_disk := by
      intro x y
      refine (D.lipschitz_on_disk ⟨φ x, hφdisk x.property⟩ ⟨φ y, hφdisk y.property⟩).trans ?_
      have hdist : ENNReal.ofReal ‖φ x - φ y‖ ≤
          (K : ℝ≥0∞) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
        simpa only [edist_dist, dist_eq_norm] using hK x.property y.property
      rw [ENNReal.ofReal_mul D.lipschitz_nonnegative, ENNReal.ofReal_coe_nnreal, mul_assoc]
      exact mul_le_mul_right hdist _
    area_integrable := hweighted.congr hdensity.symm
    area_nonnegative := by rw [harea]; exact D.area_nonnegative }
  exact ⟨D', rfl, harea, fun _ => rfl⟩

end PoincareConjecture
