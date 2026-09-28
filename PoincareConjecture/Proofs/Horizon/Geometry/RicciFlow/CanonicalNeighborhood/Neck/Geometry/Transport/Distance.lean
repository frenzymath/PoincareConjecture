import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.PathComparison







noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

theorem intrinsicEDist_le_of_path
    (g : RiemannianMetric 3 M) {U : Set M} {x y : M}
    {γ : ℝ → M} {C : ℝ≥0∞}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc (0 : ℝ) 1))
    (hγ0 : γ 0 = x) (hγ1 : γ 1 = y)
    (hγU : γ '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hL : g.pathELength γ 0 1 ≤ C) :
    intrinsicEDist g U x y ≤ C := by
  unfold intrinsicEDist
  refine (sInf_le ?_).trans hL
  exact ⟨γ, hγ, hγ0, hγ1, hγU, rfl⟩

theorem pathELength_comp_le_of_tangentNorm_le_on
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f U)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤
        C * g.tangentNorm z v)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (hγU : MapsTo γ (Icc (0 : ℝ) 1) U) :
    h.pathELength (f ∘ γ) 0 1 ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  have hγt := hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hft := hf.contMDiffAt (hU.mem_nhds (hγU (Ioo_subset_Icc_self ht)))
  rw [mfderiv_comp_apply t (hft.mdifferentiableAt one_ne_zero)
    (hγt.mdifferentiableAt one_ne_zero)]
  exact (ENNReal.ofReal_le_ofReal (hbound _ (hγU (Ioo_subset_Icc_self ht)) _)).trans_eq
    (ENNReal.ofReal_mul hC)

theorem intrinsicEDist_image_le_of_tangentNorm_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    {f : M → N} {U : Set M} {V : Set N} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f U) (hUV : MapsTo f U V)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤
        C * g.tangentNorm z v)
    (x y : M) :
    intrinsicEDist h V (f x) (f y) ≤ ENNReal.ofReal C * intrinsicEDist g U x y := by
  rw [← ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
    ENNReal.ofReal_ne_top]
  apply le_sInf
  rintro L ⟨γ, hγ, hγ0, hγ1, hγU, rfl⟩
  rw [ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
    ENNReal.ofReal_ne_top]
  have hlength := g.pathELength_comp_le_of_tangentNorm_le_on h hU hf hC.le hbound hγ
    (image_subset_iff.mp hγU)
  refine (sInf_le ?_).trans hlength
  refine ⟨f ∘ γ, hf.comp hγ (image_subset_iff.mp hγU), ?_, ?_, ?_, rfl⟩
  · exact congrArg f hγ0
  · exact congrArg f hγ1
  · exact image_subset_iff.mpr (hUV.comp (image_subset_iff.mp hγU))

end PoincareConjecture.RiemannianMetric
