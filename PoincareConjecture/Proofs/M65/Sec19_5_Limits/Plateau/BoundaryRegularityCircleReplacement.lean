import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTraceReplacement
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceCircleArc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M65Boundary

open M65StrictTrace

private theorem weakCircleArg_self (p : LoopCircle) : m65WeakCircleArg p p = Real.pi := by
  have hp : Complex.orthonormalBasisOneI.repr.symm (p : LoopPlane) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [LinearIsometryEquiv.norm_map, p.property]
    norm_num
  simp only [m65WeakCircleArg, neg_div, div_self hp, Complex.arg_neg_one]

def circleArgChart (p : LoopCircle) : OpenPartialHomeomorph LoopCircle ℝ where
  toPartialEquiv := {
    toFun := m65WeakCircleArg p
    invFun := puncturedArc p
    source := {p}ᶜ
    target := Ioo (-Real.pi) Real.pi
    map_source' := fun _ hz => weakCircleArg_mem hz
    map_target' := fun t ht => by
      change puncturedArc p t ≠ p
      intro hh
      have h := arg_puncturedArc p ht
      rw [hh, weakCircleArg_self] at h
      exact (ne_of_lt ht.2) h.symm
    left_inv' := fun z _ => puncturedArc_arg p z
    right_inv' := fun _ ht => arg_puncturedArc p ht }
  open_source := isClosed_singleton.isOpen_compl
  open_target := isOpen_Ioo
  continuousOn_toFun := fun z hz =>
    ((m65WeakCircleArg_continuousAt hz).comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  continuousOn_invFun := (puncturedArc_continuous p).continuousOn

private theorem closed_arc_frontier (p : LoopCircle) {r : ℝ}
    (hrπ : r < Real.pi)
    {z : LoopCircle} (hz : z ∈ frontier (puncturedArc p '' Icc (-r) r)) :
    m65WeakCircleArg p z = -r ∨ m65WeakCircleArg p z = r := by
  let E := circleArgChart p
  let A := puncturedArc p '' Icc (-r) r
  have hA : IsClosed A := (isCompact_Icc.image (puncturedArc_continuous p)).isClosed
  obtain ⟨t, ht, rfl⟩ := hA.closure_eq ▸ frontier_subset_closure hz
  have htπ : t ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hrπ⟩
  rw [arg_puncturedArc p htπ]
  by_contra h
  push Not at h
  have hti : t ∈ Ioo (-r) r := ⟨lt_of_le_of_ne ht.1 h.1.symm, lt_of_le_of_ne ht.2 h.2⟩
  let V := E.source ∩ E ⁻¹' Ioo (-r) r
  have hV : IsOpen V := E.continuousOn.isOpen_inter_preimage E.open_source isOpen_Ioo
  have hmem : puncturedArc p t ∈ V :=
    ⟨E.map_target htπ, by
      change m65WeakCircleArg p (puncturedArc p t) ∈ Ioo (-r) r
      rwa [arg_puncturedArc p htπ]⟩
  have hsub : V ⊆ A := by
    intro w hw
    exact ⟨E w, ⟨hw.2.1.le, hw.2.2.le⟩, E.left_inv hw.1⟩
  have hmemi : puncturedArc p t ∈ interior V := by rwa [hV.interior_eq]
  exact hz.2 (interior_mono hsub hmemi)

theorem weak_parameter_closed_arc_replacement
    (p : LoopCircle) {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi)
    (E : OpenPartialHomeomorph LoopCircle ℝ) (hconv : Convex ℝ E.target)
    (beta : C(LoopCircle, LoopCircle)) (hbeta : M65WeakCircleParameter beta)
    (hcap : MapsTo (beta ∘ puncturedArc p) (Icc (-r) r) E.source) :
    ∃ B : C(LoopCircle, LoopCircle), M65WeakCircleParameter B ∧
      (∀ t ∈ Icc (-r) r, B (puncturedArc p t) =
        E.symm (AffineMap.lineMap (E (beta (puncturedArc p (-r))))
          (E (beta (puncturedArc p r))) ((t + r) / (2 * r)))) ∧
      ∀ z ∉ puncturedArc p '' Icc (-r) r, B z = beta z := by
  let A := puncturedArc p '' Icc (-r) r
  let q := fun z => (m65WeakCircleArg p z + r) / (2 * r)
  let s := fun u => puncturedArc p (-r + (2 * r) * u)
  have hA : IsClosed A := (isCompact_Icc.image (puncturedArc_continuous p)).isClosed
  have htπ (t : ℝ) (ht : t ∈ Icc (-r) r) : t ∈ Ioo (-Real.pi) Real.pi :=
    ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hrπ⟩
  have hAcap : A ⊆ (circleArgChart p).source := by
    rintro _ ⟨t, ht, rfl⟩
    exact (circleArgChart p).map_target (htπ t ht)
  have hq : ContinuousOn q A :=
    (((circleArgChart p).continuousOn.mono hAcap).add continuousOn_const).div_const _
  have hs : Continuous s := (puncturedArc_continuous p).comp
    (continuous_const.add (continuous_const.mul continuous_id))
  have hqval (t : ℝ) (ht : t ∈ Icc (-r) r) : q (puncturedArc p t) = (t + r) / (2 * r) := by
    dsimp only [q]
    rw [arg_puncturedArc p (htπ t ht)]
  have hqA : MapsTo q A (Icc (0 : ℝ) 1) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hqval t ht]
    exact ⟨div_nonneg (by linarith [ht.1]) (by linarith),
      (div_le_one (by linarith : 0 < 2 * r)).mpr (by linarith [ht.2])⟩
  have hst (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : -r + (2 * r) * u ∈ Icc (-r) r := by
    constructor <;> nlinarith [hu.1, hu.2]
  have hsA : MapsTo s (Icc (0 : ℝ) 1) A := fun u hu => ⟨_, hst u hu, rfl⟩
  have hqs (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : q (s u) = u := by
    rw [show s u = puncturedArc p (-r + (2 * r) * u) from rfl, hqval _ (hst u hu)]
    field_simp [hr.ne']
    ring
  have hsq (z : LoopCircle) (hz : z ∈ A) : s (q z) = z := by
    obtain ⟨t, ht, rfl⟩ := hz
    rw [hqval t ht]
    dsimp only [s]
    congr 1
    field_simp [hr.ne']
    ring
  have hfront (z : LoopCircle) (hz : z ∈ frontier A) : q z = 0 ∨ q z = 1 := by
    rcases closed_arc_frontier p hrπ hz with he | he
    · left
      simp [q, he]
    · right
      dsimp only [q]
      rw [he]
      field_simp [hr.ne']
      ring
  have hbetaA : MapsTo beta A E.source := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcap ht
  obtain ⟨B, hB, hval⟩ := weak_parameter_traceInterpolation A hA q s hq hs.continuousOn
    hqA hsA hqs hsq hfront E hconv beta hbeta hbetaA
  refine ⟨B, hB, ?_, ?_⟩
  · intro t ht
    rw [hval]
    have hmem : puncturedArc p t ∈ A := mem_image_of_mem _ ht
    simp only [traceInterpolation, if_pos hmem, hqval t ht, s, mul_zero, add_zero, mul_one,
      show -r + 2 * r = r by ring]
  · intro z hz
    rw [hval]
    exact if_neg hz

theorem weak_parameter_short_arc_replacement
    (p : LoopCircle) (E : OpenPartialHomeomorph LoopCircle ℝ)
    (hconv : Convex ℝ E.target)
    (beta : C(LoopCircle, LoopCircle)) (hbeta : M65WeakCircleParameter beta)
    (hcenter : beta (puncturedArc p 0) ∈ E.source) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ B : C(LoopCircle, LoopCircle), M65WeakCircleParameter B ∧
        (∀ t ∈ Icc (-r) r, B (puncturedArc p t) =
          E.symm (AffineMap.lineMap (E (beta (puncturedArc p (-r))))
            (E (beta (puncturedArc p r))) ((t + r) / (2 * r)))) ∧
        ∀ z ∉ puncturedArc p '' Icc (-r) r, B z = beta z := by
  have hn : (beta ∘ puncturedArc p) ⁻¹' E.source ∈ 𝓝 (0 : ℝ) :=
    (beta.continuous.comp (puncturedArc_continuous p)).continuousAt.preimage_mem_nhds
      (E.open_source.mem_nhds hcenter)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hn
  let R := min (d / 2) (Real.pi / 2)
  have hR : 0 < R := lt_min (half_pos hd) (half_pos Real.pi_pos)
  have hRd : R < d := (min_le_left _ _).trans_lt (by linarith)
  have hRπ : R < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨R, hR, hRπ, ?_⟩
  intro r hr hrR
  apply weak_parameter_closed_arc_replacement p hr (hrR.trans_lt hRπ) E hconv beta hbeta
  intro t ht
  apply hball
  rw [mem_ball_zero_iff, Real.norm_eq_abs]
  exact (abs_le.mpr ht).trans_lt (hrR.trans_lt hRd)

end PoincareConjecture.M65Boundary
