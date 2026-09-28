import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.MinimalDiskRecord
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.PlaneMapRegularity
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar










set_option autoImplicit false

open Set MeasureTheory Filter Bundle Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65Attainment_continuousWithin_column {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f loopDiskSet) (v : LoopPlane) :
    ContinuousOn (fun z => (⟨f z,
      mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z v⟩ : TangentBundle (𝓡 n) M))
      loopDiskSet :=
  (hf.continuousOn_tangentMapWithin le_rfl m65LoopDisk_uniqueMDiffOn).comp
    (((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn) (fun _ hz => hz)



theorem m65Attainment_exists_within_derivative_bound (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f loopDiskSet) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ loopDiskSet, ∀ v : LoopPlane,
      g.tangentNorm (f z) (mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z v) ≤ K * ‖v‖ := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let S : LoopPlane → ℝ := fun z =>
    g.tangentNorm (f z)
        (mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      g.tangentNorm (f z)
        (mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hcol (i : Fin 2) :=
    m65Attainment_continuousWithin_column hf (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hS : ContinuousOn S loopDiskSet :=
    ((hcol 0).inner_bundle (hcol 0)).sqrt.add ((hcol 1).inner_bundle (hcol 1)).sqrt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : LoopPlane) 1).exists_bound_of_continuousOn hS
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz v
  have hsum : S z ≤ max B 0 :=
    (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))
  have hv : v = v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
  let D := mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z
  have hD : D v = v 0 • D (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      v 1 • D (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    calc
      D v = D (v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
          v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1) := congrArg D hv
      _ = _ := by erw [map_add, map_smul, map_smul]
  change ‖D v‖ ≤ max B 0 * ‖v‖
  rw [hD]
  calc
    _ ≤ ‖v 0 • D (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ +
        ‖v 1 • D (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ := norm_add_le _ _
    _ = ‖v 0‖ * ‖D (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ +
        ‖v 1‖ * ‖D (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * (‖D (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ +
        ‖D (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖) := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v 1) (norm_nonneg _))
    _ ≤ ‖v‖ * max B 0 := mul_le_mul_of_nonneg_left hsum (norm_nonneg v)
    _ = max B 0 * ‖v‖ := mul_comm _ _




theorem m65Attainment_exists_lipschitz_bound (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f loopDiskSet) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : LoopDisk,
      g.edist (f x) (f y) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨K, hK, hD⟩ := m65Attainment_exists_within_derivative_bound g hf
  refine ⟨K, hK, fun x y => ?_⟩
  let delta : ℝ → LoopPlane := AffineMap.lineMap (x : LoopPlane) (y : LoopPlane)
  have hd : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 delta :=
    (AffineMap.contDiff_lineMap (x : LoopPlane) (y : LoopPlane)).contMDiff
  have hmaps : MapsTo delta (Icc (0 : ℝ) 1) loopDiskSet := fun t ht =>
    (convex_closedBall (0 : LoopPlane) 1).lineMap_mem x.2 y.2 ht
  have hpath := hf.comp hd.contMDiffOn hmaps
  have hvel (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ delta) (Icc 0 1) t 1 =
        mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet (delta t)
          ((y : LoopPlane) - (x : LoopPlane)) := by
    rw [mfderivWithin_comp t ((hf _ (hmaps ht)).mdifferentiableWithinAt one_ne_zero)
      (hd.mdifferentiableAt one_ne_zero).mdifferentiableWithinAt hmaps
      ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)]
    rw [mfderivWithin_eq_mfderiv
      ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
      (hd.mdifferentiableAt one_ne_zero)]
    change mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet (delta t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) delta t 1) = _
    congr 1
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      (AffineMap.hasDerivAt_lineMap (a := (x : LoopPlane)) (b := (y : LoopPlane)) (x := t)).deriv
  have hlength : g.pathELength (f ∘ delta) 0 1 ≤
      ENNReal.ofReal (K * ‖(y : LoopPlane) - x‖) := by
    change Manifold.pathELength (𝓡 n) (f ∘ delta) 0 1 ≤ _
    rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (K * ‖(y : LoopPlane) - x‖) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [hvel t ht, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hD _ (hmaps ht) _)
      _ = _ := by simp
  have hdist : g.edist (f x) (f y) ≤ g.pathELength (f ∘ delta) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpath
      (by simp [delta]) (by simp [delta]) zero_le_one
  calc
    _ ≤ ENNReal.ofReal (K * ‖(y : LoopPlane) - (x : LoopPlane)‖) := hdist.trans hlength
    _ = _ := by rw [ENNReal.ofReal_mul' (norm_nonneg _), norm_sub_rev]




theorem m65Attainment_area_integrable (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f loopDiskSet) :
    IntegrableOn (m60AreaDensity g f) loopDiskSet volume := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let G : LoopPlane → Matrix (Fin 2) (Fin 2) ℝ := fun z i j =>
    g.inner (f z)
      (mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z (EuclideanSpace.basisFun (Fin 2) ℝ j))
  have hG : ContinuousOn G loopDiskSet := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mpr fun j =>
      (m65Attainment_continuousWithin_column hf _).inner_bundle
        (m65Attainment_continuousWithin_column hf _)
  have harea : ContinuousOn (fun z => Real.sqrt (max 0 (G z).det)) loopDiskSet :=
    ((continuous_const.max (continuous_id : Continuous (id : ℝ → ℝ))).comp_continuousOn
      (continuous_id.matrix_det.comp_continuousOn hG)).sqrt
  apply (harea.integrableOn_compact (isCompact_closedBall (0 : LoopPlane) 1)).congr
  filter_upwards [m65Ae_mem_openLoopDisk] with z hz
  have hnhds : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  simp only [G, m60AreaDensity, m60AreaGram, mfderivWithin_of_mem_nhds hnhds]




noncomputable def m65Attainment_spanningDisk {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (γ : C1FreeLoopSpace (M := M))
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (β : LoopCircle ≃ₜ LoopCircle) (hb : ∀ z : LoopCircle, f z = γ (β z)) :
    LipschitzSpanningDisk g γ := by
  let K := Classical.choose (m65Attainment_exists_lipschitz_bound g hf)
  have hK := (Classical.choose_spec (m65Attainment_exists_lipschitz_bound g hf)).1
  have hLip := (Classical.choose_spec (m65Attainment_exists_lipschitz_bound g hf)).2
  refine ⟨f, hf.continuousOn, ?_,
    ⟨β, β.symm, β.symm_apply_apply, β.apply_symm_apply,
      β.continuous, β.symm.continuous⟩, hb, K, hK, hLip,
    m65Attainment_area_integrable g hf, ?_⟩
  · apply (ae_restrict_iff' (isClosed_closedBall.measurableSet)).mp
    filter_upwards [m65Ae_mem_openLoopDisk] with z hz
    exact ((hf.mono Metric.ball_subset_closedBall).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt one_ne_zero
  · exact integral_nonneg (fun _ => Real.sqrt_nonneg _)

end PoincareConjecture
