import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessTarget
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUCoordinateMetric













set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem m64ChartReadable_local_metric
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (B : M → E →L[ℝ] E →L[ℝ] ℝ),
      IsOpen U ∧ p ∈ U ∧ ContinuousOn B U ∧
      (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f →
        ∀ z, f z ∈ U → ∀ i j : Fin 2,
          B (f z) (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
              m60AreaGram g f z i j := by
  obtain ⟨b, hb, L, hL⟩ := hread p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  have hb' : p ∈ c.source := by simpa only [extChartAt_source] using hb
  have hL' : (fun q => L (e q)) =ᶠ[𝓝 p] c := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hL
  have hsource : IsOpen c.source := c.open_source
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (hsource.mem_nhds hb') hL')
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun q =>
    (m60SUChartMetric g c (c q)).bilinearComp L L
  have hc : c.MDifferentiable (𝓡 n) (𝓡 n) := mdifferentiable_chart b
  have hci : ContMDiffOn (𝓡 n) (𝓡 n) 1 c.symm c.target := contMDiffOn_chart_symm
  have hmetric : ContinuousOn (fun q => m60SUChartMetric g c (c q)) U :=
    (m60SUChartMetric_continuousOn g c hci).comp
        (c.continuousOn.mono (fun q hq => (hUsub hq).1))
        (fun q hq => c.map_source (hUsub hq).1)
  refine ⟨U, B, hUopen, hpU, ?_, ?_, ?_, ?_⟩
  · apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    exact (hmetric.clm_apply continuousOn_const).clm_apply continuousOn_const
  · intro q v
    exact (g.toRiemannianMetric.toCore (c.symm (c q))).re_inner_nonneg _
  · intro q v w
    exact g.symm _ _ _
  · intro f hf z hz i j
    have hreader : (c ∘ f) =ᶠ[𝓝 z] (L ∘ (e ∘ f)) := by
      filter_upwards [hf.continuous.continuousAt (hUopen.mem_nhds hz)] with y hy
      exact (hUsub hy).2.symm
    have hd : DifferentiableAt ℝ (e ∘ f) z :=
      (contMDiff_iff_contDiff.mp (he.comp hf)).differentiable (by simp) z
    have hdf : fderiv ℝ (c ∘ f) z = L.comp (fderiv ℝ (e ∘ f) z) := by
      rw [hreader.fderiv_eq, fderiv_comp z L.differentiableAt hd, L.fderiv]
    rw [m60AreaGram_eq_SUChartMetric g c hc hf.continuous.continuousAt (hUsub hz).1,
      hdf]
    rfl

end PoincareConjecture
