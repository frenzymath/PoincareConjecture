import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.PathCompactness
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.WeakH1
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture.ReducedLengthMinimum.Variational

theorem compact_positive_forms_coercive {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set X} (hK : IsCompact K) (B : X → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcont : ContinuousOn (fun z : X × E ↦ B z.1 z.2 z.2)
      (K ×ˢ Metric.sphere (0 : E) 1) :=
    ((hB.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  obtain ⟨c, hc, hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_forall_le'
    hcont (fun z hz ↦ hpos z.1 hz.1 z.2 (by
      intro hv
      simpa [hv] using hz.2))
  refine ⟨c, hc, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm]
    simp [w, norm_smul, hn]
  have h := mul_le_mul_of_nonneg_left (hmin (x, w) ⟨hx, hw⟩) (sq_nonneg ‖v‖)
  calc
    c * ‖v‖ ^ 2 = ‖v‖ ^ 2 * c := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * B x w w := h
    _ = B x v v := by
      simp only [w, map_smul, smul_apply, smul_eq_mul]
      field_simp

end PoincareConjecture.ReducedLengthMinimum.Variational

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum.Variational

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def metricInChart (g : RiemannianMetric n M) (x y : M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (trivializationAt
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun z : M ↦ TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z →L[ℝ] ℝ) x
    (Bundle.TotalSpace.mk' _ y (g.inner y))).2

theorem metricInChart_apply (g : RiemannianMetric n M) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    metricInChart g x y v w = g.inner y
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL ℝ y v)
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL ℝ y w) := by
  have hb : y ∈
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet := hy
  unfold metricInChart
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hb hb (Set.mem_univ y)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    Bundle.Trivialization.symmL_apply _ hb]

theorem metricInChart_pos (g : RiemannianMetric n M) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < metricInChart g x y v v := by
  rw [metricInChart_apply g hy]
  apply g.pos
  intro hz
  apply hv
  have h := Bundle.Trivialization.continuousLinearMapAt_symmL (R := ℝ)
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hy v
  rw [hz, map_zero] at h
  exact h.symm

theorem metricInChart_continuousOn (g : RiemannianMetric n M) (x : M) :
    ContinuousOn (metricInChart g x) (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
  let e := trivializationAt
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun z : M ↦ TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z →L[ℝ] ℝ) x
  apply continuous_snd.comp_continuousOn (e.continuousOn.comp
    g.contMDiff.continuous.continuousOn ?_)
  intro y hy
  have hb : y ∈ e.baseSet := by
    change y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩ univ)
    exact ⟨hy, hy, mem_univ y⟩
  exact (Bundle.Trivialization.mem_source e).mpr hb

theorem metricInChart_joint_continuousOn {J : Set ℝ} (F : RicciFlow n M J) (x : M) :
    ContinuousOn (fun z : ℝ × M ↦ metricInChart (F.metric z.1) x z.2)
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) := by
  let e := trivializationAt
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun z : M ↦ TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z →L[ℝ] ℝ) x
  apply continuous_snd.comp_continuousOn (e.continuousOn.comp
    (F.smooth.continuousOn.mono (prod_mono Subset.rfl (subset_univ _))) ?_)
  intro z hz
  have hb : z.2 ∈ e.baseSet := by
    change z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩ univ)
    exact ⟨hz.2, hz.2, mem_univ _⟩
  exact (Bundle.Trivialization.mem_source e).mpr hb

noncomputable def regularizedChartMetric {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (z : ℝ × M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • metricInChart (F.metric (T - z.1 ^ 2)) x z.2

theorem regularizedChartMetric_continuousOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {a b : ℝ} {K : Set M}
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (hsrc : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContinuousOn (regularizedChartMetric F T x) (Icc a b ×ˢ K) := by
  let φ : ℝ × M → ℝ × M := fun z ↦ (T - z.1 ^ 2, z.2)
  have hφ : ContinuousOn φ (Icc a b ×ˢ K) := by
    exact ((continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd).continuousOn
  have hφmem : MapsTo φ (Icc a b ×ˢ K)
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) := by
    intro z hz
    exact ⟨htime z.1 hz.1, hsrc hz.2⟩
  have hc := (metricInChart_joint_continuousOn F x).comp hφ hφmem
  exact (continuousOn_const : ContinuousOn (fun _ : ℝ × M ↦ (1 / 2 : ℝ))
      (Icc a b ×ˢ K)).smul hc

theorem regularizedChartMetric_nonneg {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (s : ℝ) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ regularizedChartMetric F T x (s, y) v v := by
  change 0 ≤ (1 / 2 : ℝ) * metricInChart (F.metric (T - s ^ 2)) x y v v
  apply mul_nonneg (by norm_num)
  by_cases hv : v = 0
  · simp [hv]
  · exact (metricInChart_pos _ hy v hv).le

theorem chart_deriv_eq_velocity {α : ℝ → M} {x : M} {s : ℝ}
    (hs : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    deriv ((extChartAt (𝓡 n) x) ∘ α) s =
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
        ℝ (α s) (curveVelocity (n := n) α s) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hs]
  have h := mfderiv_comp_apply s (mdifferentiableAt_extChartAt hs) hα 1
  rw [mfderiv_eq_fderiv] at h
  change (fderiv ℝ ((extChartAt (𝓡 n) x) ∘ α) s) 1 = _ at h
  exact h

theorem metricInChart_deriv (g : RiemannianMetric n M) {α : ℝ → M} {x : M} {s : ℝ}
    (hs : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    metricInChart g x (α s) (deriv ((extChartAt (𝓡 n) x) ∘ α) s)
      (deriv ((extChartAt (𝓡 n) x) ∘ α) s) = referenceSpeedSq g α s := by
  rw [metricInChart_apply g hs, chart_deriv_eq_velocity hs hα,
    Bundle.Trivialization.symmL_continuousLinearMapAt _ hs]
  rfl

open MeasureTheory Filter
open scoped intervalIntegral

theorem chart_velocity_L2_bound (g : RiemannianMetric n M) (x : M)
    {K : Set M} (hK : IsCompact K)
    (hsrc : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ∃ c : ℝ, 0 < c ∧ ∀ {a b C : ℝ} (_hab : a ≤ b) (α : ℝ → M),
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b) → MapsTo α (Icc a b) K →
      IntervalIntegrable (referenceSpeedSq g α) volume a b →
      (∫ s in a..b, referenceSpeedSq g α s) ≤ C →
      ∃ hLp : MemLp (deriv ((extChartAt (𝓡 n) x) ∘ α)) 2 (volume.restrict (Icc a b)),
        ‖hLp.toLp (deriv ((extChartAt (𝓡 n) x) ∘ α))‖ ≤ Real.sqrt (c⁻¹ * C) := by
  obtain ⟨c, hc, hcoercive⟩ := compact_positive_forms_coercive hK (metricInChart g x)
    ((metricInChart_continuousOn g x).mono hsrc)
    (fun y hy v hv ↦ metricInChart_pos g (hsrc hy) v hv)
  refine ⟨c, hc, ?_⟩
  intro a b C hab α hα hαK hE hbound
  let d := deriv ((extChartAt (𝓡 n) x) ∘ α)
  have hd : AEStronglyMeasurable d (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_deriv _ _
  have hq : IntegrableOn (referenceSpeedSq g α) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hE
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc a b),
      ‖d s‖ ^ 2 ≤ c⁻¹ * referenceSpeedSq g α s := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hm := ((hα s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
      (by norm_num)
    have hb := hcoercive (α s) (hαK (Ioo_subset_Icc_self hs)) (d s)
    rw [metricInChart_deriv g (hsrc (hαK (Ioo_subset_Icc_self hs))) hm] at hb
    calc
      ‖d s‖ ^ 2 = c⁻¹ * (c * ‖d s‖ ^ 2) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * referenceSpeedSq g α s := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hc).le
  have hd2 : Integrable (fun s ↦ ‖d s‖ ^ 2) (volume.restrict (Icc a b)) := by
    apply (hq.const_mul c⁻¹).mono' (hd.norm.pow 2)
    filter_upwards [hpoint] with s hs
    change |‖d s‖ ^ 2| ≤ c⁻¹ * referenceSpeedSq g α s
    simpa only [abs_of_nonneg (sq_nonneg ‖d s‖)] using hs
  have hLp : MemLp d 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hd).mpr hd2
  refine ⟨hLp, Real.le_sqrt_of_sq_le ?_⟩
  have hnorm : ‖hLp.toLp d‖ ^ 2 = ∫ s in Icc a b, ‖d s‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hLp.coeFn_toLp] with s hs
    rw [hs, real_inner_self_eq_norm_sq]
  rw [hnorm]
  calc
    _ ≤ ∫ s in Icc a b, c⁻¹ * referenceSpeedSq g α s :=
      integral_mono_ae hd2 (hq.const_mul c⁻¹) hpoint
    _ = c⁻¹ * ∫ s in a..b, referenceSpeedSq g α s := by
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
    _ ≤ c⁻¹ * C := mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hc).le

end PoincareConjecture.ReducedLengthMinimum.Variational
