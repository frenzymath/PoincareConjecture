import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorEnergyTransport
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiMetricApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture

theorem m65SpanningDisk_exists_energy_competitor
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
      IntegrableOn (m60EnergyDensity g D'.map) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m60EnergyDensity g D'.map z) < D.area + ε := by
  let e := orthonormalBasisOneI.repr
  let HC := loopDiskSet.indicator (m60AreaGram g D.map)
  let H : ℂ → Matrix (Fin 2) (Fin 2) ℝ := HC ∘ e
  let C := (2 * D.lipschitz_constant) ^ 2
  have hs : MeasurableSet loopDiskSet := isClosed_closedBall.measurableSet
  have he : MeasurePreserving e volume volume := orthonormalBasisOneI.measurePreserving_repr
  have hei : MeasurePreserving e.symm volume volume :=
    orthonormalBasisOneI.measurePreserving_repr_symm
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hembi : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  have hpre : e ⁻¹' loopDiskSet = closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_preimage, loopDiskSet, mem_closedBall_zero_iff, e.norm_map]
  have hprei : e.symm ⁻¹' closedBall (0 : ℂ) 1 = loopDiskSet := by
    ext z
    simp only [mem_preimage, loopDiskSet, mem_closedBall_zero_iff, e.symm.norm_map]
  have her : MeasurePreserving e (volume.restrict (closedBall (0 : ℂ) 1))
      (volume.restrict loopDiskSet) := by
    simpa only [hpre] using he.restrict_preimage hs
  have heri : MeasurePreserving e.symm (volume.restrict loopDiskSet)
      (volume.restrict (closedBall (0 : ℂ) 1)) := by
    simpa only [hprei] using hei.restrict_preimage
      (s := closedBall (0 : ℂ) 1) isClosed_closedBall.measurableSet
  have hHC : Integrable HC volume :=
    (m65SpanningDisk_energy_integrable D).1.integrable_indicator hs
  have hHI : Integrable H volume := he.integrable_comp_of_integrable hHC
  have hHCb : ∀ᵐ z ∂volume, (HC z).PosSemidef ∧ ‖HC z‖ ≤ C := by
    have hb : ∀ᵐ z ∂volume, z ∈ loopDiskSet → ‖m60AreaGram g D.map z‖ ≤ C :=
      (ae_restrict_iff' hs).mp (m65SpanningDisk_gram_bound D)
    filter_upwards [hb] with z hz
    by_cases hzd : z ∈ loopDiskSet
    · simpa only [HC, indicator_of_mem hzd] using
        And.intro (m65AreaGram_posSemidef g D.map z) (hz hzd)
    · simp only [HC, indicator_of_notMem hzd, norm_zero]
      exact ⟨Matrix.PosSemidef.zero, sq_nonneg _⟩
  have hHb : ∀ᵐ z ∂volume, (H z).PosSemidef ∧ ‖H z‖ ≤ C :=
    he.quasiMeasurePreserving.ae hHCb
  have hHeq (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
      H z = m60AreaGram g D.map (e z) := by
    change loopDiskSet.indicator (m60AreaGram g D.map) (e z) = _
    exact indicator_of_mem (by rwa [← hpre] at hz) _
  have hHeqi (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      H (e.symm z) = m60AreaGram g D.map z := by
    have hz' : e.symm z ∈ closedBall (0 : ℂ) 1 := by
      change z ∈ e.symm ⁻¹' closedBall (0 : ℂ) 1
      rwa [hprei]
    simpa only [e.apply_symm_apply] using hHeq (e.symm z) hz'
  obtain ⟨K, δ, hδ, hK, hpos, hzero, hout, hWi, hWlt⟩ :=
    Matrix.exists_smooth_metric_energy_lt_area H hHI.locallyIntegrable hHb hε
  let KP := K ∘ e.symm
  have hKPc : ContDiff ℝ ∞ KP := hK.comp e.symm.toContinuousLinearEquiv.contDiff
  have hKPpos (z : LoopPlane) : (KP z).PosDef := hpos (e.symm z)
  have hKPzero : ∀ᶠ z in 𝓝 (0 : LoopPlane), KP z = δ • 1 := by
    have ht : Tendsto e.symm (𝓝 (0 : LoopPlane)) (𝓝 (0 : ℂ)) := by
      simpa only [map_zero] using e.symm.continuous.tendsto (0 : LoopPlane)
    exact ht.eventually hzero
  have hKPout (z : LoopPlane) (hz : 1 ≤ ‖z‖) : KP z = δ • 1 :=
    hout (e.symm z) (by simpa only [e.symm.norm_map] using hz)
  let W := fun z => Matrix.isothermalEnergyWeight (K z) (H z)
  let WP := fun z => Matrix.isothermalEnergyWeight (KP z) (m60AreaGram g D.map z)
  have hWEq : (W ∘ e.symm) =ᵐ[volume.restrict loopDiskSet] WP := by
    filter_upwards [ae_restrict_mem hs] with z hz
    dsimp only [Function.comp_apply, W, WP, KP]
    rw [hHeqi z hz]
  have hWPi : IntegrableOn WP loopDiskSet volume :=
    (heri.integrable_comp_of_integrable hWi).congr hWEq
  have hWPeq : (∫ z in loopDiskSet, WP z) = ∫ z in closedBall (0 : ℂ) 1, W z := by
    calc
      _ = ∫ z in loopDiskSet, W (e.symm z) := integral_congr_ae hWEq.symm
      _ = _ := heri.integral_comp hembi W
  have harea : (∫ z in closedBall (0 : ℂ) 1, Real.sqrt (H z).det) = D.area := by
    calc
      _ = ∫ z in closedBall (0 : ℂ) 1, Real.sqrt (m60AreaGram g D.map (e z)).det := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with z hz
        rw [hHeq z hz]
      _ = ∫ z in loopDiskSet, Real.sqrt (m60AreaGram g D.map z).det :=
        her.integral_comp hemb (fun z => Real.sqrt (m60AreaGram g D.map z).det)
      _ = D.area := by
        change (∫ z in loopDiskSet, Real.sqrt (m60AreaGram g D.map z).det) =
          ∫ z in loopDiskSet, parametrizedAreaDensity g D.map z
        apply integral_congr_ae
        filter_upwards [] with z
        change Real.sqrt (m60AreaGram g D.map z).det =
          Real.sqrt (max 0 (m60AreaGram g D.map z).det)
        rw [max_eq_right (m65AreaGram_posSemidef g D.map z).det_nonneg]
  obtain ⟨Φ, hΦ, hΨ, hclosed, hopen, hiso⟩ :=
    m65Exists_disk_isothermal_coordinates KP hKPc hKPpos δ hKPzero hKPout
  obtain ⟨D', harea', henergy', hE⟩ :=
    m65SpanningDisk_isothermal_reparameterize D KP hKPpos Φ hΦ hΨ hclosed hopen hiso hWPi
  refine ⟨D', harea', henergy', ?_⟩
  rw [hE, hWPeq]
  simpa only [harea] using hWlt

end PoincareConjecture
