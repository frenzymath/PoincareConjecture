import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.CompactMaximum









set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.Parabolic.Dirichlet

private lemma nonneg_deriv_of_max_on_interval {f : ℝ → ℝ} {f' a b t : ℝ}
    (ht : t ∈ Ioc a b) (hmax : IsMaxOn f (Icc a b) t)
    (hd : HasDerivWithinAt f f' (Icc a b) t) : 0 ≤ f' := by
  have hcone : a - t ∈ posTangentConeAt (Icc a b) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨ht.1.le, ht.2⟩ ⟨le_rfl, ht.1.le.trans ht.2⟩)
  have h := hmax.localize.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt hcone
  change (a - t) * f' ≤ 0 at h
  nlinarith [ht.1]


theorem nonpos_of_deriv_le_mul_at_max
    {A : Type*} [TopologicalSpace A] [CompactSpace A] {s : Set A}
    {F F' : A → ℝ → ℝ} {K a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hderiv : ∀ q ∈ s, ∀ t ∈ Ioc a b,
      HasDerivWithinAt (F q) (F' q t) (Icc a b) t)
    (hmax : ∀ q ∈ s, ∀ t ∈ Ioc a b, 0 < F q t →
      (∀ p, F p t ≤ F q t) → F' q t ≤ K * F q t)
    (hboundary : ∀ q ∉ s, ∀ t ∈ Icc a b, F q t ≤ 0)
    (hinit : ∀ q, F q a ≤ 0) :
    ∀ q t, t ∈ Icc a b → F q t ≤ 0 := by
  intro q t ht
  by_contra hnonpos
  have hpos : 0 < F q t := lt_of_not_ge hnonpos
  let G : A × ℝ → ℝ := fun p => Real.exp (-(K + 1) * (p.2 - a)) * F p.1 p.2
  have hG : ContinuousOn G (univ ×ˢ Icc a b) :=
    (show Continuous (fun p : A × ℝ => Real.exp (-(K + 1) * (p.2 - a))) by
      fun_prop).continuousOn.mul hF
  obtain ⟨⟨p, r⟩, hr, hpr⟩ :=
    (isCompact_univ.prod isCompact_Icc).exists_isMaxOn ⟨(q, t), trivial, ht⟩ hG
  have hmaxqt : G (q, t) ≤ G (p, r) := hpr ⟨trivial, ht⟩
  have hGr : 0 < G (p, r) :=
    (mul_pos (Real.exp_pos _) hpos).trans_le hmaxqt
  have hFr : 0 < F p r := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hGr
  have hps : p ∈ s := by
    by_contra hp
    exact (not_lt_of_ge (hboundary p hp r hr.2)) hFr
  have har : a < r := lt_of_le_of_ne hr.2.1 (by
    intro heq
    subst r
    exact (not_lt_of_ge (hinit p)) hFr)
  have hr' : r ∈ Ioc a b := ⟨har, hr.2.2⟩
  have hspace : ∀ z, F z r ≤ F p r := by
    intro z
    have h := hpr (a := (z, r)) ⟨trivial, hr.2⟩
    change G (z, r) ≤ G (p, r) at h
    exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp h
  have htime : IsMaxOn (fun z => G (p, z)) (Icc a b) r :=
    fun z hz => hpr (a := (p, z)) ⟨trivial, hz⟩
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-(K + 1) * (z - a)))
      (Real.exp (-(K + 1) * (r - a)) * (-(K + 1))) r := by
    simpa [id_eq] using (((hasDerivAt_id r).sub_const a).const_mul (-(K + 1))).exp
  have hge := nonneg_deriv_of_max_on_interval hr' htime
    (hexp.hasDerivWithinAt.mul (hderiv p hps r hr'))
  have hle := hmax p hps r hr' hFr hspace
  have hexppos := Real.exp_pos (-(K + 1) * (r - a))
  nlinarith

end Poincare.Parabolic.Dirichlet
