import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRetention
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlPath
import PoincareConjecture.Proofs.M34.Mathlib.FirstExitOpen
import PoincareConjecture.Proofs.M36.MetricComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}

private theorem initial_height_le_intrinsic (N : EpsilonNeck g)
    {y z : M} (hz : z ∈ N.central_sphere) :
    ENNReal.ofReal (N.scale / 2 * |(N.coordinate_inverse y).2|) ≤
      intrinsicEDist g (N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere) y z := by
  apply le_sInf
  rintro L ⟨p, hp, hp0, hp1, hmem, rfl⟩
  have hzero : (N.coordinate_inverse z).2 = 0 := (M36.neck_central_iff N).mp hz |>.2
  have hcarrier : MapsTo p (Icc (0 : ℝ) 1) N.carrier := by
    intro t ht
    exact ((M36.neck_retained_iff N).mp (hmem (mem_image_of_mem p ht))).1
  have hheight := N.height_displacement_le_pathELength zero_le_one hp hcarrier
  rw [hp0, hp1, hzero, zero_sub, abs_neg] at hheight
  have hcancel : ENNReal.ofReal (N.scale / 2) * ENNReal.ofReal (2 / N.scale) = 1 := by
    rw [← ENNReal.ofReal_mul (div_nonneg N.scale_pos.le (by norm_num))]
    have h : N.scale / 2 * (2 / N.scale) = 1 := by field_simp [N.scale_pos.ne']
    rw [h, ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (N.scale / 2) * ENNReal.ofReal |(N.coordinate_inverse y).2| :=
      ENNReal.ofReal_mul (div_nonneg N.scale_pos.le (by norm_num))
    _ ≤ ENNReal.ofReal (N.scale / 2) *
        (ENNReal.ofReal (2 / N.scale) * g.pathELength p 0 1) :=
      mul_le_mul_right hheight _
    _ = g.pathELength p 0 1 := by rw [← mul_assoc, hcancel, one_mul]



theorem source_initial_old_height_le_path_length
    (R : MetricSurgeryResult g0 I) {y : M}
    (hy : y ∈ I.neck.region (-I.neck.epsilon⁻¹) 0)
    (p : ℝ → R.output.carrier)
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc (0 : ℝ) 1))
    (hp0 : p 0 = R.collapse y) (hp1 : p 1 = R.tip) :
    ENNReal.ofReal (I.neck.scale / 2 * |(I.neck.coordinate_inverse y).2|) ≤
      R.metric.pathELength p 0 1 := by
  let cap := R.cap_map '' g0.metric.ball 0 (g0.cylindrical_end.radius + 4)
  let V := I.neck.region (-I.neck.epsilon⁻¹) 0 ∪ I.neck.central_sphere
  have hstart : p 0 ∈ (closure cap)ᶜ := by
    rw [hp0, R.cap_exterior]
    exact mem_image_of_mem R.collapse hy
  have htip : R.tip ∈ cap := by
    refine ⟨0, ?_, R.cap_map_tip⟩
    change g0.metric.edist 0 0 < ENNReal.ofReal (g0.cylindrical_end.radius + 4)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (by linarith [g0.cylindrical_end.radius_pos])
  have hfinish : p 1 ∉ (closure cap)ᶜ := by
    rw [hp1]
    exact not_not_intro (subset_closure htip)
  obtain ⟨t, ht, hfrontier, hbefore⟩ := hp.continuousOn.exists_first_exit_open
    zero_le_one isClosed_closure.isOpen_compl hstart hfinish
  have hcentral : p t ∈ R.collapse '' I.neck.central_sphere := by
    rw [R.cap_boundary]
    exact frontier_closure_subset (frontier_compl (closure cap) ▸ hfrontier)
  obtain ⟨z, hz, hzt⟩ := hcentral
  have hprefix : MapsTo p (Icc (0 : ℝ) t) (R.collapse '' V) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hst | rfl
    · have hneg : p s ∈ R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 0 := by
        rw [← R.cap_exterior]
        exact hbefore s ⟨hs.1, hst⟩
      exact image_mono subset_union_left hneg
    · exact ⟨z, Or.inr hz, hzt⟩
  let clock : ℝ → ℝ := fun s => t * s
  let path := p ∘ clock
  have hclock : ContDiff ℝ 1 clock := contDiff_const.mul contDiff_id
  have hclockMap : MapsTo clock (Icc (0 : ℝ) 1) (Icc 0 t) := by
    intro s hs
    exact ⟨mul_nonneg ht.1.le hs.1,
      (mul_le_mul_of_nonneg_left hs.2 ht.1.le).trans_eq (mul_one t)⟩
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 path (Icc 0 1) :=
    (hp.mono hsub).comp hclock.contMDiff.contMDiffOn hclockMap
  have hpath0 : path 0 = R.collapse y := by
    simpa only [path, Function.comp_apply, clock, mul_zero] using hp0
  have hpath1 : path 1 = R.collapse z := by
    simpa only [path, Function.comp_apply, clock, mul_one] using hzt.symm
  have hmon : MonotoneOn clock (Icc (0 : ℝ) 1) := by
    intro s _ r _ hsr
    exact mul_le_mul_of_nonneg_left hsr ht.1.le
  have hd : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) p (Icc (clock 0) (clock 1)) := by
    simpa only [clock, mul_zero, mul_one] using
      (hp.mono hsub).mdifferentiableOn one_ne_zero
  have hlength : R.metric.pathELength path 0 1 = R.metric.pathELength p 0 t := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : R.output.carrier → Type _) :=
      ⟨R.metric.toRiemannianMetric⟩
    have h := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) zero_le_one
      hmon (hclock.differentiable one_ne_zero).differentiableOn hd
    convert! h using 1
    simp only [clock, mul_zero, mul_one]
    rfl
  have hint : intrinsicEDist R.metric (R.collapse '' V) (R.collapse y) (R.collapse z) ≤
      R.metric.pathELength path 0 1 := by
    apply sInf_le
    exact ⟨path, hpath, hpath0, hpath1,
      image_subset_iff.mpr (fun s hs => hprefix (hclockMap hs)), rfl⟩
  rw [R.retained_closed_isometry y (Or.inl hy) z (Or.inr hz)] at hint
  exact (initial_height_le_intrinsic I.neck hz).trans
    (hint.trans (hlength.le.trans (M36.metric_pathELength_mono R.metric p le_rfl ht.2)))

end PoincareConjecture.M47
