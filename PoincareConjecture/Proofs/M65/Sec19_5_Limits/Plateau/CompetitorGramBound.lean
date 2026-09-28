import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorGram
import PoincareConjecture.Proofs.M40.Mathlib.SmoothChartDistance
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65TangentNorm_mfderiv_le_lipschitz
    (g : RiemannianMetric n M) {f : LoopPlane → M} {s : Set LoopPlane} {z : LoopPlane}
    (hs : s ∈ 𝓝 z) (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z) (C : ℝ≥0)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, g.edist (f x) (f y) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal ‖x - y‖) (v : LoopPlane) :
    g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z v) ≤ 2 * C * ‖v‖ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f z)
  have he : e.MDifferentiable (𝓡 n) (𝓡 n) := mdifferentiable_chart _
  have hx : f z ∈ e.source := mem_chart_source _ _
  let chi := M40.normalizedSmoothChart e he hx
  have hchi : f z ∈ chi.source := by
    simpa only [chi, M40.normalizedSmoothChart_source] using hx
  obtain ⟨R, hR, _, _, hforward⟩ :=
    M40.normalizedSmoothChart_exists_lipschitz_ball e he hx
      contMDiffOn_chart contMDiffOn_chart_symm 2 (by norm_num)
  have hfl : LipschitzOnWith C f s := by
    intro x hx y hy
    change g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y
    simpa only [edist_dist, dist_eq_norm] using hLip x hx y hy
  let U := (s ∩ f ⁻¹' chi.source) ∩ (chi ∘ f) ⁻¹' ball (chi (f z)) R
  have hU : U ∈ 𝓝 z := inter_mem
    (inter_mem hs (hf.continuousAt.preimage_mem_nhds (chi.open_source.mem_nhds hchi)))
    (((chi.continuousAt hchi).comp hf.continuousAt).preimage_mem_nhds (ball_mem_nhds _ hR))
  have hlocal : LipschitzOnWith (2 * C) (chi ∘ f) U := by
    apply hforward.comp (hfl.mono (fun _ hu => hu.1.1))
    intro y hy
    exact ⟨chi (f y), hy.2, chi.left_inv hy.1.2⟩
  have hD : ‖fderiv ℝ (chi ∘ f) z‖ ≤ 2 * (C : ℝ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      norm_fderiv_le_of_lipschitzOn ℝ hU hlocal
  have hchiDiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ, TangentSpace (𝓡 n) (f z)) chi (f z) :=
    ((M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart).contMDiffAt
      (chi.open_source.mem_nhds hchi)).mdifferentiableAt (by simp)
  have hident : fderiv ℝ (chi ∘ f) z v = mfderiv (𝓡 2) (𝓡 n) f z v := by
    calc
      _ = NormedSpace.fromTangentSpace (chi (f z))
          (mfderiv (𝓡 2) 𝓘(ℝ, TangentSpace (𝓡 n) (f z)) (chi ∘ f) z v) := by
        rw [mfderiv_eq_fderiv]
        rfl
      _ = NormedSpace.fromTangentSpace (chi (f z))
          (mfderiv (𝓡 n) 𝓘(ℝ, TangentSpace (𝓡 n) (f z)) chi (f z)
            (mfderiv (𝓡 2) (𝓡 n) f z v)) := by rw [mfderiv_comp z hchiDiff hf]; rfl
      _ = _ := M40.normalizedSmoothChart_mfderiv_apply e he hx _
  have hnorm : g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z v) =
      ‖mfderiv (𝓡 2) (𝓡 n) f z v‖ := by
    simpa only [RiemannianMetric.tangentNorm] using!
      (norm_eq_sqrt_real_inner (mfderiv (𝓡 2) (𝓡 n) f z v)).symm
  rw [hnorm, ← hident]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hD (norm_nonneg v))

theorem m65SpanningDisk_gram_bound {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ) :
    ∀ᵐ z ∂volume.restrict loopDiskSet,
      ‖m60AreaGram g D.map z‖ ≤ (2 * D.lipschitz_constant) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let C : ℝ≥0 := ⟨D.lipschitz_constant, D.lipschitz_nonnegative⟩
  have hC : ENNReal.ofReal D.lipschitz_constant = (C : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal D.lipschitz_nonnegative
  have hsphere : ∀ᵐ z ∂volume, z ∉ sphere (0 : LoopPlane) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : LoopPlane) 1)
  filter_upwards [ae_restrict_of_ae D.ae_manifold_differentiable,
    ae_restrict_of_ae hsphere, ae_restrict_mem (isClosed_closedBall.measurableSet)]
      with z hdiff hn hz
  have hlt : ‖z‖ < 1 :=
    (lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz)).resolve_right
      (fun heq => hn (mem_sphere_zero_iff_norm.mpr heq))
  have hnhds : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hlt)) ball_subset_closedBall
  have hbound (v : LoopPlane) : ‖mfderiv (𝓡 2) (𝓡 3) D.map z v‖ ≤
      2 * D.lipschitz_constant * ‖v‖ := by
    have hh := m65TangentNorm_mfderiv_le_lipschitz g hnhds (hdiff hz) C
      (fun x hx y hy => by
        simpa only [hC] using D.lipschitz_on_disk ⟨x, hx⟩ ⟨y, hy⟩) v
    have heq : g.tangentNorm (D.map z) (mfderiv (𝓡 2) (𝓡 3) D.map z v) =
        ‖mfderiv (𝓡 2) (𝓡 3) D.map z v‖ := by
      simpa only [RiemannianMetric.tangentNorm] using!
        (norm_eq_sqrt_real_inner (mfderiv (𝓡 2) (𝓡 3) D.map z v)).symm
    rw [heq] at hh
    exact hh
  apply (Matrix.norm_le_iff (sq_nonneg (2 * D.lipschitz_constant))).mpr
  intro i j
  change ‖inner ℝ (mfderiv (𝓡 2) (𝓡 3) D.map z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (mfderiv (𝓡 2) (𝓡 3) D.map z (EuclideanSpace.basisFun (Fin 2) ℝ j))‖ ≤ _
  have hi := hbound (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hj := hbound (EuclideanSpace.basisFun (Fin 2) ℝ j)
  rw [(EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one] at hi hj
  calc
    _ ≤ ‖mfderiv (𝓡 2) (𝓡 3) D.map z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ *
        ‖mfderiv (𝓡 2) (𝓡 3) D.map z (EuclideanSpace.basisFun (Fin 2) ℝ j)‖ :=
      norm_inner_le_norm _ _
    _ ≤ (2 * D.lipschitz_constant) * (2 * D.lipschitz_constant) :=
      mul_le_mul hi hj (norm_nonneg _) (mul_nonneg (by norm_num) D.lipschitz_nonnegative)
    _ = _ := (pow_two _).symm

end PoincareConjecture
