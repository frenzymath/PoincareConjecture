import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorCoordinates
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.SpanningDiskReparameterization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65SpanningDisk_isothermal_reparameterize
    {g : RiemannianMetric 3 M} {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ)
    (K : LoopPlane → Matrix (Fin 2) (Fin 2) ℝ) (hpos : ∀ z, (K z).PosDef)
    (Φ : LoopPlane ≃ₜ LoopPlane)
    (hΦ : ContDiff ℝ ∞ (Φ : LoopPlane → LoopPlane))
    (hΨ : ContDiff ℝ ∞ (Φ.symm : LoopPlane → LoopPlane))
    (hclosed : ∀ z, ‖Φ z‖ ≤ 1 ↔ ‖z‖ ≤ 1)
    (hopen : ∀ z, ‖Φ z‖ < 1 ↔ ‖z‖ < 1)
    (hiso : ∀ z ∈ loopDiskSet, ∃ c : ℝ, 0 < c ∧
      let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (fderiv ℝ (Φ : LoopPlane → LoopPlane) z).toLinearMap
      B.transpose * K (Φ z) * B = c • 1)
    (hweight : IntegrableOn
      (fun z => Matrix.isothermalEnergyWeight (K z) (m60AreaGram g D.map z))
      loopDiskSet volume) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
      IntegrableOn (m60EnergyDensity g D'.map) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m60EnergyDensity g D'.map z) =
        ∫ z in loopDiskSet, Matrix.isothermalEnergyWeight (K z) (m60AreaGram g D.map z) := by
  have hs : MeasurableSet loopDiskSet := isClosed_closedBall.measurableSet
  have hΦdisk : MapsTo Φ loopDiskSet loopDiskSet := fun z hz =>
    mem_closedBall_zero_iff.mpr ((hclosed z).mpr (mem_closedBall_zero_iff.mp hz))
  have hΨdisk : MapsTo Φ.symm loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    exact (hclosed (Φ.symm z)).mp (by
      simpa only [Φ.apply_symm_apply] using (mem_closedBall_zero_iff.mp hz))
  have hcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖Φ z‖ = 1 :=
    le_antisymm ((hclosed z).mpr hz.le) (not_lt.mp (fun hlt => by
      have h := (hopen z).mp hlt
      linarith))
  have hcircle' (z : LoopPlane) (hz : ‖z‖ = 1) : ‖Φ.symm z‖ = 1 := by
    apply le_antisymm
    · exact (hclosed (Φ.symm z)).mp (by simpa only [Φ.apply_symm_apply] using hz.le)
    · apply not_lt.mp
      intro hlt
      have h := (hopen (Φ.symm z)).mpr hlt
      rw [Φ.apply_symm_apply, hz] at h
      exact (lt_irrefl 1) h
  have himage : Φ '' loopDiskSet = loopDiskSet := by
    apply Subset.antisymm hΦdisk.image_subset
    intro z hz
    exact ⟨Φ.symm z, hΨdisk hz, Φ.apply_symm_apply z⟩
  have hdiff (z : LoopPlane) : DifferentiableAt ℝ (Φ : LoopPlane → LoopPlane) z :=
    (hΦ.differentiable (by simp)).differentiableAt
  have hDpull : ∀ᵐ z ∂volume, z ∈ loopDiskSet →
      MDifferentiableAt (𝓡 2) (𝓡 3) D.map (Φ z) := by
    let N := {y | y ∈ loopDiskSet ∧ ¬MDifferentiableAt (𝓡 2) (𝓡 3) D.map y}
    have hN : volume N = 0 := by
      simpa only [Classical.not_imp, N] using ae_iff.mp D.ae_manifold_differentiable
    have hnull : volume (Φ.symm '' N) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (fun _ _ => (hΨ.differentiable (by simp)).differentiableAt.differentiableWithinAt) hN
    apply ae_iff.mpr
    apply measure_mono_null _ hnull
    intro z hz
    have hz' : z ∈ loopDiskSet ∧ ¬MDifferentiableAt (𝓡 2) (𝓡 3) D.map (Φ z) :=
      Classical.not_imp.mp hz
    exact ⟨Φ z, ⟨hΦdisk hz'.1, hz'.2⟩, Φ.symm_apply_apply z⟩
  let W := fun z => Matrix.isothermalEnergyWeight (K z) (m60AreaGram g D.map z)
  have hdensity : m60EnergyDensity g (D.map ∘ Φ) =ᵐ[volume.restrict loopDiskSet]
      fun z => |(fderiv ℝ (Φ : LoopPlane → LoopPlane) z).det| • W (Φ z) := by
    filter_upwards [(ae_restrict_iff' hs).mpr hDpull, ae_restrict_mem hs] with z hDz hz
    obtain ⟨c, hc, hisoz⟩ := hiso z hz
    let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    let B := LinearMap.toMatrix b b (fderiv ℝ (Φ : LoopPlane → LoopPlane) z).toLinearMap
    have hdet : B.det = (fderiv ℝ (Φ : LoopPlane → LoopPlane) z).det :=
      LinearMap.det_toMatrix b _
    rw [m60EnergyDensity, m65AreaGram_comp g D.map Φ z hDz (hdiff z)]
    change (1 / 2 : ℝ) * (B.transpose * m60AreaGram g D.map (Φ z) * B).trace = _
    simpa only [hdet, smul_eq_mul, W] using
      Matrix.isothermal_energy_change (K (Φ z)) B (m60AreaGram g D.map (Φ z))
        (hpos (Φ z)) hc hisoz
  have hderiv : ∀ z ∈ loopDiskSet, HasFDerivWithinAt (Φ : LoopPlane → LoopPlane)
      (fderiv ℝ (Φ : LoopPlane → LoopPlane) z) loopDiskSet z :=
    fun z _ => (hdiff z).hasFDerivAt.hasFDerivWithinAt
  have hweighted : IntegrableOn
      (fun z => |(fderiv ℝ (Φ : LoopPlane → LoopPlane) z).det| • W (Φ z))
      loopDiskSet volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hderiv
      Φ.injective.injOn W).mp
    rw [himage]
    exact hweight
  have henergy : (∫ z in loopDiskSet, m60EnergyDensity g (D.map ∘ Φ) z) =
      ∫ z in loopDiskSet, W z := by
    calc
      _ = ∫ z in loopDiskSet, |(fderiv ℝ (Φ : LoopPlane → LoopPlane) z).det| • W (Φ z) :=
        integral_congr_ae hdensity
      _ = ∫ z in Φ '' loopDiskSet, W z :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv
          Φ.injective.injOn W).symm
      _ = _ := by rw [himage]
  obtain ⟨D', hmap, harea, _⟩ := m65SpanningDisk_reparameterize D Φ Φ.symm
    (fun _ _ => hΦ.contDiffAt.of_le (by simp))
    (fun _ _ => hΨ.contDiffAt.of_le (by simp)) hΦdisk hΨdisk hcircle hcircle'
    (fun z _ => Φ.symm_apply_apply z) (fun z _ => Φ.apply_symm_apply z)
  refine ⟨D', harea, ?_, ?_⟩
  · rw [hmap]
    exact hweighted.congr hdensity.symm
  · rw [hmap]
    exact henergy

end PoincareConjecture
