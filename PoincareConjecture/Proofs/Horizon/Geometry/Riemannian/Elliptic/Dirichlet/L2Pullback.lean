import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartEnergy

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem map_coordinate_density (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    ((volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict
      e.source).map e = g.volumeMeasure.restrict e.target := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hm : AEMeasurable e ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  rw [← hmap, AEMeasurable.map_map_of_aemeasurable hm
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)]
  calc
    _ = (g.volumeMeasure.restrict e.target).map id := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
      exact e.right_inv hy
    _ = _ := Measure.map_id

theorem exists_map_compact_coordinate_le (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ (volume.restrict K).map e ≤ c • g.volumeMeasure := by
  obtain ⟨a, ha, hρ⟩ := LeviCivitaData.Dirichlet.exists_chart_density_lower_bound
    (g := g) e he hei hK hKs
  let c := ENNReal.ofReal a
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hct : c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  let ν := (volume.withDensity (fun x => ENNReal.ofReal
    (g.pullbackVolumeDensity e x))).restrict e.source
  have hmeasure : c • volume.restrict K ≤ ν := by
    calc
      _ = (volume.restrict K).withDensity (fun _ => c) := (withDensity_const c).symm
      _ ≤ (volume.restrict K).withDensity
          (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal (hρ y hy)
      _ = (volume.withDensity
          (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict K :=
        (restrict_withDensity hK.measurableSet _).symm
      _ ≤ _ := Measure.restrict_mono hKs le_rfl
  have hbound := smul_le_smul_left c⁻¹ hmeasure
  rw [smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul] at hbound
  refine ⟨c⁻¹, ENNReal.inv_ne_top.mpr hc, ?_⟩
  have hm : AEMeasurable e (c⁻¹ • ν) := by
    apply AEMeasurable.smul_measure
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  calc
    _ ≤ (c⁻¹ • ν).map e := Measure.map_mono_of_aemeasurable hbound hm
    _ = c⁻¹ • g.volumeMeasure.restrict e.target := by
      rw [Measure.map_smul, g.map_coordinate_density e he hei]
    _ ≤ _ := smul_le_smul_left c⁻¹ Measure.restrict_le_self

theorem exists_compactL2Pullback (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ T : Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 (volume.restrict K),
      ∀ v : Lp ℝ 2 g.volumeMeasure,
        (T v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict K] fun x => v (e x) := by
  obtain ⟨c, hc, hbound⟩ := g.exists_map_compact_coordinate_le e he hei hK hKs
  have hm : AEMeasurable e (volume.restrict K) :=
    (e.continuousOn.mono hKs).aemeasurable hK.measurableSet
  let R : Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 ((volume.restrict K).map e) :=
    Lp.LpToLpOfMeasureLeSMul hc hbound
  have hp : MeasurePreserving (hm.mk e) (volume.restrict K) ((volume.restrict K).map e) :=
    ⟨hm.measurable_mk, Measure.map_congr hm.ae_eq_mk.symm⟩
  let P := (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ (hm.mk e) hp).toContinuousLinearMap
  refine ⟨P.comp R, fun v => ?_⟩
  have hR : (R v : M → ℝ) =ᵐ[(volume.restrict K).map e] v :=
    Lp.coeFn_LpToLpOfMeasureLeSMul hc hbound v
  have hP : (P (R v) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict K]
      fun x => (R v) (hm.mk e x) := Lp.coeFn_compMeasurePreserving (R v) hp
  filter_upwards [hP, hp.quasiMeasurePreserving.ae_eq hR, hm.ae_eq_mk] with x hx hxR hxe
  change (P (R v)) x = v (e x)
  dsimp only [Function.comp_apply] at hxR
  rw [hx, hxR, ← hxe]

def compactL2Pullback (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (g.exists_compactL2Pullback e he hei hK hKs).choose

theorem compactL2Pullback_ae (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : Lp ℝ 2 g.volumeMeasure) :
    (g.compactL2Pullback e he hei hK hKs v : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict K] fun x => v (e x) :=
  (g.exists_compactL2Pullback e he hei hK hKs).choose_spec v

theorem ae_comp_on_compact (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {f h : M → ℝ} (hfh : f =ᵐ[g.volumeMeasure] h) :
    (fun x => f (e x)) =ᵐ[volume.restrict K] fun x => h (e x) := by
  obtain ⟨c, -, hbound⟩ := g.exists_map_compact_coordinate_le e he hei hK hKs
  have hac : (volume.restrict K).map e ≪ g.volumeMeasure :=
    Measure.absolutelyContinuous_of_le_smul hbound
  exact ae_of_ae_map ((e.continuousOn.mono hKs).aemeasurable hK.measurableSet)
    (hac.ae_eq hfh)

def localL2Pullback (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K S : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hSK : S ⊆ K) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 (volume.restrict S) :=
  (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono hSK (le_refl volume))).comp
      (g.compactL2Pullback e he hei hK hKs)

theorem localL2Pullback_ae (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K S : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hSK : S ⊆ K) (v : Lp ℝ 2 g.volumeMeasure) :
    (g.localL2Pullback e he hei hK hKs hSK v : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict S] fun x => v (e x) := by
  have hrestrict : volume.restrict S ≤ volume.restrict K := Measure.restrict_mono hSK le_rfl
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using hrestrict) (g.compactL2Pullback e he hei hK hKs v)).trans
      ((g.compactL2Pullback_ae e he hei hK hKs v).filter_mono (ae_mono hrestrict))

end PoincareConjecture.RiemannianMetric
