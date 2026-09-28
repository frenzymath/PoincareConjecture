import PoincareConjecture.Proofs.M47.SeedImageBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.Proofs.M47

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

private theorem inverse_quadratic_le
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞) (C : ℝ)
    (hlower : ∀ x ∈ D.source, ∀ w : TangentSpace (𝓡 3) x,
      g.inner x w w ≤ C ^ 2 * h.inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x w)
        (mfderiv (𝓡 3) (𝓡 3) D x w))
    {y : Y} (hy : y ∈ D.target) (w : TangentSpace (𝓡 3) y) :
    g.inner (D.symm y) (mfderiv (𝓡 3) (𝓡 3) D.symm y w)
      (mfderiv (𝓡 3) (𝓡 3) D.symm y w) ≤ C ^ 2 * h.inner y w w := by
  have he : D.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨D.mdifferentiableOn (by simp), D.symm.mdifferentiableOn (by simp)⟩
  have hd : (mfderiv (𝓡 3) (𝓡 3) D (D.symm y)).comp
      (mfderiv (𝓡 3) (𝓡 3) D.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) y) := he.comp_symm_deriv hy
  have hw : mfderiv (𝓡 3) (𝓡 3) D (D.symm y)
      (mfderiv (𝓡 3) (𝓡 3) D.symm y w) = w := congrArg (fun A => A w) hd
  have hm := hlower (D.symm y) (D.map_target hy)
    (mfderiv (𝓡 3) (𝓡 3) D.symm y w)
  rw [hw] at hm
  have hright : D.toPartialEquiv (D.symm.toPartialEquiv y) = y := D.right_inv hy
  exact hm.trans_eq (congrArg (fun z : Y => C ^ 2 * h.inner z w w) hright)



theorem horizon_ball_subset_image [RegularSpace X] [T2Space Y]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞) {C : ℝ} (hC : 0 < C)
    (hlower : ∀ x ∈ D.source, ∀ w : TangentSpace (𝓡 3) x,
      g.inner x w w ≤ C ^ 2 * h.inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x w)
        (mfderiv (𝓡 3) (𝓡 3) D x w))
    (p : X) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball p r)))
    (hsource : closure (g.ball p r) ⊆ D.source) :
    h.ball (D p) (r / C) ⊆ D '' g.ball p r := by
  have hopen : IsOpen (g.ball p r) :=
    isOpen_Iio.preimage ((M36.metric_edist_continuous g).comp
      (continuous_const.prodMk continuous_id))
  have hDs := D.toOpenPartialHomeomorph.isOpen_image_of_subset_source hopen
    (subset_closure.trans hsource)
  have hclosure := D.toOpenPartialHomeomorph.image_closure_of_compact_buffer hcompact hsource
  have hfrontier := D.toOpenPartialHomeomorph.image_frontier_of_compact_buffer
    hopen hcompact hsource
  change IsOpen (D '' g.ball p r) at hDs
  change D '' closure (g.ball p r) = closure (D '' g.ball p r) at hclosure
  change D '' frontier (g.ball p r) = frontier (D '' g.ball p r) at hfrontier
  have hp : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have htarget : closure (D '' g.ball p r) ⊆ D.target := by
    rw [← hclosure]
    rintro _ ⟨x, hx, rfl⟩
    exact D.map_source (hsource hx)
  let k := m01RescaledMetric g (C⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr hC))
  apply h.ball_subset_of_inverse_length_barrier k D.symm hDs (mem_image_of_mem D hp)
  · intro y hy
    exact D.symm.contMDiffOn.contMDiffAt (D.open_target.mem_nhds (htarget hy))
  · intro y hy w
    have hm := inverse_quadratic_le g h D C hlower (htarget hy) w
    change (m01RescaledMetric g (C⁻¹ ^ 2) _).inner _ _ _ ≤ _
    rw [m01RescaledMetric_inner]
    calc
      _ ≤ C⁻¹ ^ 2 * (C ^ 2 * h.inner y w w) :=
        mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = _ := by field_simp
  · intro y hy
    rw [← hfrontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hleftP : D.symm.toPartialEquiv (D.toPartialEquiv p) = p :=
      D.left_inv (hsource (subset_closure hp))
    have hleftX : D.symm.toPartialEquiv (D.toPartialEquiv x) = x := D.left_inv (hsource hx.1)
    rw [hleftP, hleftX]
    have hnot : x ∉ g.ball p r := by simpa only [hopen.interior_eq] using hx.2
    have hdist : ENNReal.ofReal r ≤ g.edist p x := le_of_not_gt hnot
    change ENNReal.ofReal (r / C) ≤ (m01RescaledMetric g (C⁻¹ ^ 2) _).edist p x
    rw [m01RescaledMetric_edist, Real.sqrt_sq (inv_pos.mpr hC).le]
    calc
      ENNReal.ofReal (r / C) = ENNReal.ofReal C⁻¹ * ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul (inv_pos.mpr hC).le]
        congr 1
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ _ := mul_le_mul_right hdist _



theorem horizon_target_ball_volume_le_source [T3Space X] [T3Space Y]
    [SecondCountableTopology X] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞) {C : ℝ} (hC : 0 < C)
    (hlower : ∀ x ∈ D.source, ∀ w : TangentSpace (𝓡 3) x,
      g.inner x w w ≤ C ^ 2 * h.inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x w)
        (mfderiv (𝓡 3) (𝓡 3) D x w))
    (hupper : ∀ x ∈ D.source, ∀ w : TangentSpace (𝓡 3) x,
      h.inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x w)
        (mfderiv (𝓡 3) (𝓡 3) D x w) ≤ C ^ 2 * g.inner x w w)
    (p : X) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball p r)))
    (hsource : closure (g.ball p r) ⊆ D.source) :
    calibratedMetricVolume h (h.ball (D p) (r / C)) ≤
      ENNReal.ofReal C ^ 3 * calibratedMetricVolume g (g.ball p r) := by
  have hcover := horizon_ball_subset_image g h D hC hlower p hr hcompact hsource
  have hnorm : ∀ x ∈ D.source, ∀ w : TangentSpace (𝓡 3) x,
      h.tangentNorm (D x) (mfderiv (𝓡 3) (𝓡 3) D x w) ≤ C * g.tangentNorm x w := by
    intro x hx w
    unfold RiemannianMetric.tangentNorm
    apply (Real.sqrt_le_sqrt (hupper x hx w)).trans_eq
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
  have hopen : IsOpen (g.ball p r) :=
    isOpen_Iio.preimage ((M36.metric_edist_continuous g).comp
      (continuous_const.prodMk continuous_id))
  exact (measure_mono hcover).trans
    (M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le g h
      D.toOpenPartialHomeomorph (D.contMDiffOn.of_le (by simp)) hC hnorm
      hopen.measurableSet (subset_closure.trans hsource))

end PoincareConjecture.Proofs.M47
