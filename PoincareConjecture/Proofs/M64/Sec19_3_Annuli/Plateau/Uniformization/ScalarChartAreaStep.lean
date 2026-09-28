import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarChartReplacement













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)





theorem scalar_exists_chart_area_step
    (g : RiemannianMetric n M) (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (f : Plane → M) {O V K : Set Plane} (hO : IsOpen O) (hV : IsOpen V)
    (hf : ContinuousOn f O) (hfV : MapsTo f V e.source)
    {L : ℝ≥0} (hcoord : LipschitzOnWith L (e ∘ f) V)
    {rho : Plane → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hcompact : HasCompactSupport rho) (hrange : ∀ x, rho x ∈ Icc 0 1)
    (hsupp : tsupport rho ⊆ V) (hK : MeasurableSet K) (hCK : tsupport rho ⊆ K)
    (harea : IntegrableOn (m60AreaDensity g f) K) {eps : ℝ} (heps : 0 < eps) :
    ∃ F : Plane → M, ∃ B : ℝ≥0,
      ContinuousOn F O ∧ LipschitzOnWith B (e ∘ F) V ∧ MapsTo F V e.source ∧
      (∀ x, x ∉ tsupport rho → F =ᶠ[𝓝 x] f) ∧
      (∀ x, ContMDiffAt (𝓡 2) (𝓡 n) 1 f x → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
      (∀ x, rho =ᶠ[𝓝 x] 1 → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
      (∀ x, dist (F x) (f x) < eps) ∧
      IntegrableOn (m60AreaDensity g F) K ∧
      (∫ x in K, m60AreaDensity g F x) < (∫ x in K, m60AreaDensity g f x) + eps := by
  obtain ⟨G, B, hGc, hGl, hGmaps, hGa, hGp, hGs, hGv, hGI, hGA⟩ :=
    scalar_exists_chart_area_replacements g e he hei f hO hV hf hfV hcoord
      hrho hcompact hrange hsupp
  have hsmall := hGA.eventually (gt_mem_nhds (show
    (∫ x in tsupport rho, m60AreaDensity g f x) <
      (∫ x in tsupport rho, m60AreaDensity g f x) + eps by linarith))
  obtain ⟨j, hjv, hja⟩ := ((Metric.tendstoUniformly_iff.mp hGv) eps heps).and hsmall |>.exists
  have hdiff : EqOn (m60AreaDensity g (G j)) (m60AreaDensity g f) (K \ tsupport rho) :=
    fun x hx => m60AreaDensity_congr_of_eventuallyEq g (hGa j x hx.2)
  have hdiffI : IntegrableOn (m60AreaDensity g (G j)) (K \ tsupport rho) := by
    apply (harea.mono_set sdiff_subset).congr
    filter_upwards [ae_restrict_mem (hK.diff hcompact.measurableSet)] with x hx
    exact (hdiff hx).symm
  have hGIwhole : IntegrableOn (m60AreaDensity g (G j)) K := by
    simpa only [sdiff_union_of_subset hCK] using hdiffI.union (hGI j)
  have hdecomp (w : Plane → M) (hw : IntegrableOn (m60AreaDensity g w) K) :
      (∫ x in K, m60AreaDensity g w x) =
        (∫ x in K \ tsupport rho, m60AreaDensity g w x) +
          ∫ x in tsupport rho, m60AreaDensity g w x := by
    simpa only [sdiff_union_of_subset hCK] using
      setIntegral_union disjoint_sdiff_self_left hcompact.measurableSet
        (hw.mono_set sdiff_subset) (hw.mono_set hCK)
  refine ⟨G j, B, hGc j, hGl j, hGmaps j, hGa j, hGp j, hGs j,
    (fun x => (dist_comm _ _).trans_lt (hjv x)), hGIwhole, ?_⟩
  rw [hdecomp (G j) hGIwhole, hdecomp f harea,
    setIntegral_congr_fun (hK.diff hcompact.measurableSet) hdiff]
  linarith

end PoincareConjecture.M64Uniformization
