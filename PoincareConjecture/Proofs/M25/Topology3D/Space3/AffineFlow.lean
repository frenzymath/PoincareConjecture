import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)



theorem boundedFlow_eq_affine_on (c x : E) {d : ℝ} (hd : 0 < d)
    (hc : ∀ t ∈ Ioo (-d) d, f (x + t • c) = c) :
    EqOn (boundedFlow f hK hL x) (fun t => x + t • c) (Ioo (-d) d) := by
  have hzero : (0 : ℝ) ∈ Ioo (-d) d := by constructor <;> linarith
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun _ : ℝ => f) (s := fun _ => univ)
    (fun _ _ => hK.lipschitzOnWith) hzero
  · exact fun t _ => ⟨boundedFlow_hasDerivAt f hK hL x t, mem_univ _⟩
  · intro t ht
    refine ⟨?_, mem_univ _⟩
    rw [hc t ht]
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const c).const_add x
  · simp only [boundedFlow_zero, zero_smul, add_zero]



theorem boundedFlow_eq_affine_of_large_norm (c : E) {R : ℝ}
    (hc : ∀ y, R < ‖y‖ → f y = c) (x : E) (hx : R + ‖c‖ + 1 < ‖x‖)
    (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    boundedFlow f hK hL x t = x + t • c := by
  apply boundedFlow_eq_affine_on f hK hL c x zero_lt_one ?_ ht
  intro u hu
  apply hc
  have huabs : |u| < 1 := abs_lt.mpr hu
  have huc : ‖u • c‖ ≤ ‖c‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg c) huabs.le
  have hnorm : ‖x‖ ≤ ‖x + u • c‖ + ‖u • c‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (x + u • c) (u • c)
  linarith



theorem boundedFlow_smooth_strip_of_compact_perturbation [FiniteDimensional ℝ E]
    (hf : ContDiff ℝ ∞ f) (c : E) (hs : HasCompactSupport (fun x => f x - c)) :
    ∃ d > (0 : ℝ),
      ContDiffOn ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2)
        (univ ×ˢ Ioo (-d) d) := by
  classical
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall (0 : E)
  have hc (y : E) (hy : R < ‖y‖) : f y = c := by
    apply sub_eq_zero.mp
    apply image_eq_zero_of_notMem_tsupport (f := fun x => f x - c)
    intro hy'
    have := hR hy'
    rw [mem_closedBall_zero_iff] at this
    exact (not_le.mpr hy) this
  choose U d hU hx hd hF using boundedFlow_local_smooth f hK hL hf
  let W : Set (E × ℝ) := ⋃ x : E, U x ×ˢ Ioo (-d x) (d x)
  have hWo : IsOpen W := isOpen_iUnion fun x => (hU x).prod isOpen_Ioo
  have hWF : ContDiffOn ℝ ∞
      (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2) W := by
    intro p hp
    obtain ⟨x, hpx⟩ := mem_iUnion.mp hp
    exact ((hF x).contDiffAt (((hU x).prod isOpen_Ioo).mem_nhds hpx)).contDiffWithinAt
  let C : Set E := closedBall 0 (R + ‖c‖ + 1)
  have hcover : C ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact mem_iUnion.mpr ⟨x, hx x, by constructor <;> linarith [hd x]⟩
  obtain ⟨A, B, _, hB, hA, hzero, hAB⟩ :=
    generalized_tube_lemma (isCompact_closedBall 0 (R + ‖c‖ + 1))
      isCompact_singleton hWo hcover
  obtain ⟨r, hr, hrB⟩ :=
    Metric.mem_nhds_iff.mp (hB.mem_nhds (hzero (mem_singleton 0)))
  have hIB : Ioo (-r) r ⊆ B := by
    intro t ht
    apply hrB
    change dist t 0 < r
    rw [Real.dist_eq, sub_zero]
    exact abs_lt.mpr ht
  let e := min r 1
  have he : 0 < e := lt_min hr zero_lt_one
  have her : e ≤ r := min_le_left _ _
  have he1 : e ≤ 1 := min_le_right _ _
  refine ⟨e, he, fun p hp => ?_⟩
  by_cases hpk : p.1 ∈ C
  · have hpW : p ∈ W := hAB ⟨hA hpk, hIB ⟨by linarith [hp.2.1],
        by linarith [hp.2.2]⟩⟩
    exact (hWF.contDiffAt (hWo.mem_nhds hpW)).contDiffWithinAt
  · have hpt : p.2 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have ho : IsOpen (Cᶜ ×ˢ Ioo (-1 : ℝ) 1) :=
      isClosed_closedBall.isOpen_compl.prod isOpen_Ioo
    have heq : (fun q : E × ℝ => boundedFlow f hK hL q.1 q.2) =ᶠ[𝓝 p]
        (fun q => q.1 + q.2 • c) := by
      filter_upwards [ho.mem_nhds ⟨hpk, hpt⟩] with q hq
      have hqnorm : R + ‖c‖ + 1 < ‖q.1‖ := by
        simpa only [C, mem_compl_iff, mem_closedBall_zero_iff, not_le] using hq.1
      exact boundedFlow_eq_affine_of_large_norm f hK hL c hc q.1 hqnorm q.2 hq.2
    exact ((contDiffAt_fst.add (contDiffAt_snd.smul_const c)).congr_of_eventuallyEq
      heq).contDiffWithinAt



theorem boundedFlow_contDiff_of_compact_perturbation [FiniteDimensional ℝ E]
    (hf : ContDiff ℝ ∞ f) (c : E) (hs : HasCompactSupport (fun x => f x - c)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2) := by
  obtain ⟨d, hd, hstrip⟩ :=
    boundedFlow_smooth_strip_of_compact_perturbation f hK hL hf c hs
  exact boundedFlow_contDiff_of_smooth_strip f hK hL hd hstrip

end PoincareConjecture.M25.Topology3D
