import PoincareConjecture.Definitions.Ch03.RicciFlow










set_option autoImplicit false

open Bundle ContinuousLinearMap Filter Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}


theorem backward_metric_continuousAt
    (hwindow : Icc (T - τmax) T ⊆ J)
    (z : M × ℝ) (hz : z ∈ univ ×ˢ Ioo 0 τmax) :
    ContinuousAt (fun w : M × ℝ ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ)
      w.1 ((F.metric (T - w.2)).inner w.1)) z := by
  have htime : T - z.2 ∈ Ioo (T - τmax) T := by
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hnhds : J ×ˢ (univ : Set M) ∈ 𝓝 (T - z.2, z.1) :=
    Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨htime, mem_univ _⟩)
      (fun _ hw ↦ ⟨hwindow ⟨hw.1.1.le, hw.1.2.le⟩, hw.2⟩)
  have hmetric : ContinuousAt (fun w : ℝ × M ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ)
      w.2 ((F.metric w.1).inner w.2)) (T - z.2, z.1) :=
    F.smooth.continuousOn.continuousAt hnhds
  exact hmetric.comp (f := fun w : M × ℝ ↦ (T - w.2, w.1))
    ((continuous_const.sub continuous_snd).prodMk continuous_fst).continuousAt

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 100000 in


theorem slice_tangentNorm_locally_le_terminal
    (hwindow : Icc (T - τmax) T ⊆ J)
    (z : M × ℝ) (hz : z ∈ univ ×ˢ Ioo 0 τmax) :
    ∃ U : Set (M × ℝ), IsOpen U ∧ z ∈ U ∧ U ⊆ univ ×ˢ Ioo 0 τmax ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ U, ∀ v : TangentSpace (𝓡 n) w.1,
        (F.metric (T - w.2)).tangentNorm w.1 v ≤
          K * (F.metric T).tangentNorm w.1 v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric T).inner, (F.metric T).toContinuousRiemannianMetric.continuous,
      fun _ _ _ ↦ rfl⟩⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) z.1
  let B : M × ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun w ↦
    inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun q ↦ TangentSpace (𝓡 n) q →L[ℝ] ℝ)
      z.1 w.1 z.1 w.1 ((F.metric (T - w.2)).inner w.1)
  have hB : ContinuousAt B z := by
    have h := backward_metric_continuousAt (F := F) hwindow z hz
    rw [continuousAt_hom_bundle] at h
    exact h.2
  let A : ℝ := ‖B z‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hnorm : Continuous (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ ‖L‖) :=
    continuous_norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  have hBbound : ∀ᶠ w in 𝓝 z, ‖B w‖ < A :=
    (hnorm.continuousAt.comp hB) (eventually_lt_nhds (lt_add_one _))
  obtain ⟨L, hL, hLbound⟩ := eventually_norm_trivializationAt_lt
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) z.1
  have hesource : ∀ᶠ q in 𝓝 z.1, q ∈ e.baseSet :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' z.1)
  have hnear : {w : M × ℝ | w ∈ univ ×ˢ Ioo 0 τmax ∧ w.1 ∈ e.baseSet ∧
      ‖B w‖ < A ∧ ‖e.continuousLinearMapAt ℝ w.1‖ < L} ∈ 𝓝 z := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz,
      continuous_fst.continuousAt hesource, hBbound,
      continuous_fst.continuousAt hLbound] with w htime hsource hB' hL'
    exact ⟨htime, hsource, hB', hL'⟩
  obtain ⟨U, hU, hUopen, hzU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, hUopen, hzU, fun w hw ↦ (hU hw).1,
    Real.sqrt A * L, mul_nonneg (Real.sqrt_nonneg _) hL.le, ?_⟩
  intro w hw v
  obtain ⟨_, hsource, hBw, hLw⟩ := hU hw
  let v' := e.continuousLinearMapAt ℝ w.1 v
  have hv' : ‖v'‖ ≤ L * ‖v‖ :=
    (e.continuousLinearMapAt ℝ w.1).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hLw.le (norm_nonneg _))
  have hvalue : (F.metric (T - w.2)).inner w.1 v v = B w v' v' := by
    dsimp only [B]
    rw [inCoordinates_apply_eq₂ hsource hsource (mem_univ _)]
    change _ = (Bundle.Trivial.trivialization M ℝ).linearMapAt ℝ w.1
      ((F.metric (T - w.2)).inner w.1 (e.symm w.1 v') (e.symm w.1 v'))
    simp only [v', Trivialization.continuousLinearMapAt_apply,
      Trivialization.symm_linearMapAt e hsource,
      Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  have hsq : (F.metric (T - w.2)).inner w.1 v v ≤
      (Real.sqrt A * L * ‖v‖) ^ 2 := calc
    _ = B w v' v' := hvalue
    _ ≤ ‖B w v' v'‖ := le_abs_self _
    _ ≤ ‖B w‖ * ‖v'‖ * ‖v'‖ := (B w).le_opNorm₂ v' v'
    _ ≤ A * (L * ‖v‖) * (L * ‖v‖) := by gcongr
    _ = (Real.sqrt A * L * ‖v‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA.le]
      ring
  have hvnorm : (F.metric T).tangentNorm w.1 v = ‖v‖ :=
    (norm_eq_sqrt_real_inner v).symm
  rw [hvnorm]
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hsq⟩

end PoincareConjecture.M10
