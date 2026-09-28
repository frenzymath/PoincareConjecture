import PoincareConjecture.Proofs.M08.PathRecovery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.M08

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_uniform_affine_tube {a b : ℝ} (u η : ℝ → E)
    (hu : ContinuousOn u (Icc a b)) (hη : ContinuousOn η (Icc a b))
    {K : Set E} (huK : u '' Icc a b ⊆ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, |ε| < δ →
      MapsTo (fun s ↦ u s + ε • η s) (Icc a b) K := by
  obtain ⟨r, hr, hmargin⟩ := (isCompact_Icc.image_of_continuousOn hu).exists_cthickening_subset_open
    isOpen_interior huK
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hη
  let C := max D 0
  have hC : 0 ≤ C := le_max_right _ _
  have hCp : 0 < C + 1 := by positivity
  let δ := min 1 (r / (C + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hr hCp)
  have hδr : δ * (C + 1) ≤ r := (le_div_iff₀ hCp).mp (min_le_right _ _)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro ε hε s hs
  have hηbound : ‖η s‖ ≤ C := (hD s hs).trans (le_max_left _ _)
  have hnorm : ‖ε • η s‖ < r := by
    rw [norm_smul, Real.norm_eq_abs]
    have hmul := mul_le_mul_of_nonneg_left hηbound (abs_nonneg ε)
    have hmul' := mul_le_mul_of_nonneg_right hε.le hC
    nlinarith
  apply interior_subset (hmargin ?_)
  apply Metric.mem_cthickening_of_dist_le _ (u s) _ _ (mem_image_of_mem u hs)
  simpa only [dist_eq_norm, add_sub_cancel_left] using hnorm.le

theorem chartL2_affine_primitive {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → E) (w : ChartL2 E a b)
    (hw : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r)
    (η ν : ℝ → E) (hη : ContinuousOn η (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt η (ν s) s)
    (hν : MemLp ν 2 (volume.restrict (Icc a b))) (ε : ℝ) :
    ∃ v : ChartL2 E a b,
      (v : ℝ → E) =ᵐ[volume.restrict (Icc a b)] (fun s ↦ w s + ε • ν s) ∧
      ∀ s ∈ Icc a b, u s + ε • η s = u a + ε • η a + ∫ r in a..s, v r := by
  have hLp : MemLp (fun s ↦ w s + ε • ν s) 2 (volume.restrict (Icc a b)) :=
    (Lp.memLp w).add (hν.const_smul ε)
  let v := hLp.toLp (fun s ↦ w s + ε • ν s)
  refine ⟨v, hLp.coeFn_toLp, ?_⟩
  intro s hs
  have hsub : uIcc a s ⊆ uIcc a b := by
    rw [uIcc_of_le hs.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right hs.2
  have hwint0 : IntervalIntegrable w volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ((Lp.memLp w).integrable (by norm_num))
  have hwint := hwint0.mono_set hsub
  have hνint : IntervalIntegrable ν volume a s := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mpr
    exact IntegrableOn.mono_set (hν.integrable (by norm_num)) (Icc_subset_Icc_right hs.2)
  have heq : (∫ r in a..s, v r) = ∫ r in a..s, w r + ε • ν r := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hs.1]
    exact ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hs.2)) le_rfl) hLp.coeFn_toLp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
    (hη.mono (Icc_subset_Icc_right hs.2))
    (fun r hr ↦ hd r ⟨hr.1, hr.2.trans_le hs.2⟩) hνint
  have hεν : IntervalIntegrable (fun r ↦ ε • ν r) volume a s := hνint.smul ε
  rw [heq, intervalIntegral.integral_add hwint hεν,
    intervalIntegral.integral_smul, hFTC, hw s hs, smul_sub]
  abel

universe uM

variable {n : ℕ} {M : Type uM} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_chart_affine_buffer {a b : ℝ} (x : M)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContinuousOn η (Icc a b)) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      K ⊆ (extChartAt (𝓡 n) x).target ∧
      (extChartAt (𝓡 n) x ∘ γ) '' Icc a b ⊆ interior K ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, |ε| < δ →
        MapsTo (fun s ↦ extChartAt (𝓡 n) x (γ s) + ε • η s) (Icc a b) K := by
  let e := extChartAt (𝓡 n) x
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have hu : ContinuousOn (e ∘ γ) (Icc a b) :=
    (continuousOn_extChartAt (I := 𝓡 n) x).comp hγ hsrc'
  have htarget : (e ∘ γ) '' Icc a b ⊆ e.target := by
    rintro _ ⟨s, hs, rfl⟩
    exact e.map_source (hsrc' hs)
  obtain ⟨K, hK, huK, hKt⟩ := exists_compact_between
    (isCompact_Icc.image_of_continuousOn hu) (isOpen_extChartAt_target (I := 𝓡 n) x) htarget
  obtain ⟨δ, hδ, hδ1, hδK⟩ := exists_uniform_affine_tube (e ∘ γ) η hu hη huK
  exact ⟨K, hK, hKt, huK, δ, hδ, hδ1, hδK⟩

theorem chart_affine_competitor {a b : ℝ} (hab : a ≤ b)
    (x : M) (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hw : ∀ s ∈ Icc a b, extChartAt (𝓡 n) x (γ s) =
      extChartAt (𝓡 n) x (γ a) + ∫ r in a..s, w r)
    (η ν : ℝ → EuclideanSpace ℝ (Fin n))
    (hη : ContinuousOn η (Icc a b)) (hd : ∀ s ∈ Ioo a b, HasDerivAt η (ν s) s)
    (hν : MemLp ν 2 (volume.restrict (Icc a b)))
    (hηa : η a = 0) (hηb : η b = 0) (ε : ℝ)
    (htarget : MapsTo (fun s ↦ extChartAt (𝓡 n) x (γ s) + ε • η s) (Icc a b)
      (extChartAt (𝓡 n) x).target) :
    ∃ (ξ : ℝ → M) (v : ChartL2 (EuclideanSpace ℝ (Fin n)) a b),
      ContinuousOn ξ (Icc a b) ∧ ξ a = γ a ∧ ξ b = γ b ∧
      MapsTo ξ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      (∀ s, ξ s = (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x (γ s) + ε • η s)) ∧
      ((v : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc a b)]
        (fun s ↦ w s + ε • ν s)) ∧
      (∀ s ∈ Icc a b, extChartAt (𝓡 n) x (ξ s) =
        extChartAt (𝓡 n) x (γ s) + ε • η s) ∧
      ∀ s ∈ Icc a b, extChartAt (𝓡 n) x (ξ s) =
        extChartAt (𝓡 n) x (ξ a) + ∫ r in a..s, v r := by
  let e := extChartAt (𝓡 n) x
  let u : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have hu : ContinuousOn u (Icc a b) :=
    (continuousOn_extChartAt (I := 𝓡 n) x).comp hγ hsrc'
  obtain ⟨v, hv, hprimitive⟩ := chartL2_affine_primitive hab u w hw η ν hη hd hν ε
  let ξ : ℝ → M := fun s ↦ e.symm (u s + ε • η s)
  have hξ : ContinuousOn ξ (Icc a b) :=
    (continuousOn_extChartAt_symm (I := 𝓡 n) x).comp (hu.add (hη.const_smul ε)) htarget
  have hξa : ξ a = γ a := by
    simp only [ξ, hηa, smul_zero, add_zero]
    exact e.left_inv (hsrc' ⟨le_rfl, hab⟩)
  have hξb : ξ b = γ b := by
    simp only [ξ, hηb, smul_zero, add_zero]
    exact e.left_inv (hsrc' ⟨hab, le_rfl⟩)
  have hξsrc : MapsTo ξ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    intro s hs
    simpa only [ξ, u, Function.comp_apply, e, extChartAt_source] using e.map_target (htarget hs)
  have hcoord (s : ℝ) (hs : s ∈ Icc a b) : e (ξ s) = u s + ε • η s :=
    e.right_inv (htarget hs)
  refine ⟨ξ, v, hξ, hξa, hξb, hξsrc, fun _ ↦ rfl, hv, hcoord, ?_⟩
  intro s hs
  change e (ξ s) = e (ξ a) + _
  rw [hcoord s hs, hcoord a ⟨le_rfl, hab⟩]
  exact hprimitive s hs

end PoincareConjecture.M08
