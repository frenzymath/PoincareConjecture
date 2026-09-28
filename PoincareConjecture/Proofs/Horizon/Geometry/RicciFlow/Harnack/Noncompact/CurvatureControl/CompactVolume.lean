import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeMeasure
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_volumeMeasure_of_subset
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    {S K : Set M} (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K) :
    HasDerivAt (fun s => ((F.metric s).volumeMeasure S).toReal)
      (-(∫ y in S, (F.connection t).scalarCurvature y
        ∂(F.metric t).volumeMeasure)) t := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have hfinite (s : ℝ) {A : Set M} (hAK : A ⊆ K) :
      (F.metric s).volumeMeasure A ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hAK)
      ((F.metric s).volumeMeasure_lt_top_of_isCompact hK)).ne
  have hint : IntegrableOn (F.connection t).scalarCurvature K
      (F.metric t).volumeMeasure :=
    hD.contMDiff_scalarCurvature.continuous.continuousOn.integrableOn_compact hK
  let P : Set M → Prop := fun U => ∃ V : Set M, MeasurableSet V ∧ U ⊆ V ∧
    ∀ A : Set M, MeasurableSet A → A ⊆ V ∩ K →
      HasDerivAt (fun s => ((F.metric s).volumeMeasure A).toReal)
        (-(∫ y in A, (F.connection t).scalarCurvature y
          ∂(F.metric t).volumeMeasure)) t
  have hp : P K := by
    apply hK.induction_on (p := P)
    · refine ⟨∅, MeasurableSet.empty, Subset.rfl, ?_⟩
      intro A hA hAK
      have hAe : A = ∅ := subset_empty_iff.mp (hAK.trans inter_subset_left)
      simp only [hAe, measure_empty, ENNReal.toReal_zero, setIntegral_empty, neg_zero]
      exact hasDerivAt_const t 0
    · rintro U V hUV ⟨W, hW, hVW, hd⟩
      exact ⟨W, hW, hUV.trans hVW, hd⟩
    · rintro U W ⟨V, hV, hUV, hdV⟩ ⟨Z, hZ, hWZ, hdZ⟩
      refine ⟨V ∪ Z, hV.union hZ, union_subset_union hUV hWZ, ?_⟩
      intro A hA hAK
      have hAK' : A ⊆ K := hAK.trans inter_subset_right
      have hd₁ := hdV (A ∩ V) (hA.inter hV)
        (fun _ hx => ⟨hx.2, hAK' hx.1⟩)
      have hd₂ := hdZ (A \ V) (hA.diff hV)
        (fun _ hx => ⟨(hAK hx.1).1.resolve_left hx.2, hAK' hx.1⟩)
      have hfun : (fun s => ((F.metric s).volumeMeasure A).toReal) =
          (fun s => ((F.metric s).volumeMeasure (A ∩ V)).toReal +
            ((F.metric s).volumeMeasure (A \ V)).toReal) := by
        funext s
        rw [← measure_inter_add_sdiff A hV,
          ENNReal.toReal_add (hfinite s (inter_subset_left.trans hAK'))
            (hfinite s (sdiff_subset.trans hAK'))]
      rw [hfun]
      apply (hd₁.add hd₂).congr_deriv
      have heq := integral_inter_add_sdiff hV (hint.mono_set hAK')
      linarith
    · intro x hx
      let e := (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
      obtain ⟨L, hL, hxL, hLe⟩ :=
        exists_compact_subset e.open_target (mem_chart_source _ x)
      refine ⟨interior L, mem_nhdsWithin_of_mem_nhds
        (isOpen_interior.mem_nhds hxL), interior L, isOpen_interior.measurableSet,
        Subset.rfl, ?_⟩
      intro A hA hAL
      have hAL' : A ⊆ L := (hAL.trans inter_subset_left).trans interior_subset
      have hAe : A ⊆ e.target := hAL'.trans hLe
      have hpre : MeasurableSet (e.symm '' A) := by
        rw [e.symm_image_eq_source_inter_preimage hAe]
        have hm := e.continuousOn.measurable_piecewise
          (g := fun _ => x) continuousOn_const e.open_source.measurableSet
        have h := e.open_source.measurableSet.inter (hA.preimage hm)
        convert h using 1
        ext z
        by_cases hz : z ∈ e.source <;> simp [hz]
      have hLc : IsCompact (e.symm '' L) :=
        hL.image_of_continuousOn (e.symm.continuousOn.mono hLe)
      have hLcE : e.symm '' L ⊆ e.source := image_subset_iff.mpr
        (fun y hy => e.map_target (hLe hy))
      have hd := F.hasDerivAt_volumeMeasure_image_of_subset ht hD e
        contMDiffOn_chart_symm contMDiffOn_chart hpre hLc (image_mono hAL') hLcE
      have heA : e '' (e.symm '' A) = A := e.image_symm_image_of_subset_target hAe
      rwa [heA] at hd
  obtain ⟨V, hV, hKV, hd⟩ := hp
  exact hd S hS (fun _ hx => ⟨hKV (hSK hx), hSK hx⟩)

theorem hasDerivAt_volumeMeasure
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    {K : Set M} (hK : IsCompact K) :
    HasDerivAt (fun s => ((F.metric s).volumeMeasure K).toReal)
      (-(∫ y in K, (F.connection t).scalarCurvature y
        ∂(F.metric t).volumeMeasure)) t :=
  F.hasDerivAt_volumeMeasure_of_subset ht hD hK.measurableSet hK Subset.rfl

end PoincareConjecture.RicciFlow
