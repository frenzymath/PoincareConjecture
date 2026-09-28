import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_WeightedFocusingCover
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture

private theorem exists_periodic_weighted_projection
    {f : ℝ → ℝ} {P : ℝ} (hf : Continuous f) (hfnonneg : ∀ x, 0 ≤ f x)
    (hfp : Function.Periodic f P) (hP : 0 < P)
    {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Icc (0 : ℝ) (2 * P)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) P ∧
      B ∩ Icc (0 : ℝ) P ⊆ E ∧
      (fun x => x - P) '' (B ∩ Icc P (2 * P)) ⊆ E ∧
      (∫ x in E, f x) ≤ ∫ x in B, f x := by
  let C := B ∩ Icc (0 : ℝ) P
  let D := (fun x : ℝ => x + P) ⁻¹' (B \ Icc (0 : ℝ) P)
  let E := insert 0 (C ∪ D)
  have hC : MeasurableSet C := hB.inter measurableSet_Icc
  have hD : MeasurableSet D :=
    (continuous_id.add continuous_const).measurable (hB.diff measurableSet_Icc)
  have hCsub : C ⊆ Icc (0 : ℝ) P := inter_subset_right
  have hDsub : D ⊆ Icc (0 : ℝ) P := by
    intro x hx
    have hxB := hBsub hx.1
    have hlt : P < x + P := by
      by_contra h
      exact hx.2 ⟨hxB.1, le_of_not_gt h⟩
    exact ⟨by linarith, by linarith [hxB.2]⟩
  have hE : MeasurableSet E := (hC.union hD).insert 0
  have hEsub : E ⊆ Icc (0 : ℝ) P := by
    rintro x (rfl | hx)
    · exact ⟨le_rfl, hP.le⟩
    · exact union_subset hCsub hDsub hx
  have hCi : IntegrableOn f C := hf.integrableOn_Icc.mono_set hCsub
  have hDi : IntegrableOn f D := hf.integrableOn_Icc.mono_set hDsub
  have hBi : IntegrableOn f B := hf.integrableOn_Icc.mono_set hBsub
  have himage : (fun x : ℝ => x + P) '' D = B \ Icc (0 : ℝ) P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x - P, by simpa only [D, mem_preimage, sub_add_cancel] using hx,
        sub_add_cancel x P⟩
  have hshift : (∫ x in D, f x) = ∫ x in B \ Icc (0 : ℝ) P, f x := by
    have h := integral_image_eq_integral_abs_deriv_smul hD
      (fun x _ => ((hasDerivAt_id x).add_const P).hasDerivWithinAt)
      (fun x _ y _ h => add_right_cancel h) f
    simp only [id_eq] at h
    rw [himage] at h
    have hperiod : (fun x => f (x + P)) = f := funext hfp
    simpa only [abs_one, one_smul, hperiod] using h.symm
  have hunion : (∫ x in C ∪ D, f x) ≤ (∫ x in C, f x) + ∫ x in D, f x := by
    have hset : C ∪ D = C ∪ (D \ C) := by
      ext x
      simp only [mem_union, Set.mem_sdiff]
      tauto
    rw [hset, setIntegral_union
      (disjoint_left.mpr (fun _ hx hy => hy.2 hx)) (hD.diff hC)
      hCi (hDi.mono_set sdiff_subset)]
    exact add_le_add le_rfl (setIntegral_mono_set (s := D \ C) hDi
      (Eventually.of_forall hfnonneg) (Eventually.of_forall sdiff_subset))
  refine ⟨E, hE, hEsub, ?_, ?_, ?_⟩
  · intro x hx
    exact mem_insert_of_mem 0 (Or.inl hx)
  · rintro x ⟨y, hy, rfl⟩
    by_cases hEq : y = P
    · simp only [hEq, sub_self, E, mem_insert_iff, true_or]
    · apply mem_insert_of_mem
      apply Or.inr
      change y - P + P ∈ B \ Icc (0 : ℝ) P
      rw [sub_add_cancel]
      exact ⟨hy.1, fun h => hEq (le_antisymm h.2 hy.2.1)⟩
  · calc
      (∫ x in E, f x) = ∫ x in C ∪ D, f x :=
        setIntegral_congr_set (insert_ae_eq_self 0 (C ∪ D))
      _ ≤ (∫ x in C, f x) + ∫ x in D, f x := hunion
      _ = ∫ x in B, f x := by
        rw [hshift]
        exact integral_inter_add_sdiff measurableSet_Icc hBi

theorem m64Intrinsic_exists_cyclic_weighted_focusing_cover
    {f g : ℝ → ℝ} {P A τ : ℝ}
    (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hg : Continuous g) (hgnonneg : ∀ x, 0 ≤ g x)
    (hfp : Function.Periodic f P) (hgp : Function.Periodic g P)
    (hP : 0 < P) (hA : 0 ≤ A) (hτ : 3 < τ)
    (T : Set (ℝ × ℝ))
    (hT : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < P)
    (hfocus : ∀ p ∈ T,
      ((∫ x in p.1..p.2, f x) ≤ A * ∫ x in p.1..p.2, g x) ∨
      ((∫ x in p.2..p.1 + P, f x) ≤ A * ∫ x in p.2..p.1 + P, g x)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) P ∧
      (∀ p ∈ T, Icc p.1 p.2 ⊆ E ∨ (Icc p.2 P ∪ Icc 0 p.1) ⊆ E) ∧
      (∫ x in E, f x) ≤ (2 * τ * A) * ∫ x in (0 : ℝ)..P, g x := by
  let Q : Set (ℝ × ℝ) := {q |
    (q ∈ T ∧ (∫ x in q.1..q.2, f x) ≤ A * ∫ x in q.1..q.2, g x) ∨
    ∃ p ∈ T, q = (p.2, p.1 + P) ∧
      (∫ x in p.2..p.1 + P, f x) ≤ A * ∫ x in p.2..p.1 + P, g x}
  have hQ (q : ℝ × ℝ) (hq : q ∈ Q) :
      0 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ 2 * P := by
    rcases hq with ⟨hq, _⟩ | ⟨p, hp, rfl, _⟩
    · obtain ⟨ha, hab, hb⟩ := hT q hq
      exact ⟨ha, hab, by linarith⟩
    · obtain ⟨ha, hab, hb⟩ := hT p hp
      exact ⟨ha.trans hab.le, by dsimp; linarith, by dsimp; linarith⟩
  have hQfocus (q : ℝ × ℝ) (hq : q ∈ Q) :
      (∫ x in q.1..q.2, f x) ≤ A * ∫ x in q.1..q.2, g x := by
    rcases hq with ⟨_, h⟩ | ⟨p, _, rfl, h⟩ <;> exact h
  obtain ⟨B, hB, hBsub, hcover, hbound⟩ :=
    m64Intrinsic_exists_weighted_focusing_cover hf hfpos hg hgnonneg
      (by positivity : 0 < 2 * P) hA hτ Q hQ hQfocus
  obtain ⟨E, hE, hEsub, hleft, hright, hproj⟩ :=
    exists_periodic_weighted_projection hf (fun x => (hfpos x).le) hfp hP hB hBsub
  refine ⟨E, hE, hEsub, ?_, ?_⟩
  · intro p hp
    obtain ⟨ha, hab, hb⟩ := hT p hp
    rcases hfocus p hp with h | h
    · left
      intro x hx
      exact hleft ⟨hcover p (Or.inl ⟨hp, h⟩) hx,
        ⟨ha.trans hx.1, hx.2.trans hb.le⟩⟩
    · right
      have hq : (p.2, p.1 + P) ∈ Q := Or.inr ⟨p, hp, rfl, h⟩
      intro x hx
      rcases hx with hx | hx
      · exact hleft ⟨hcover _ hq ⟨hx.1, by linarith [hx.2]⟩,
          ⟨ha.trans (hab.le.trans hx.1), hx.2⟩⟩
      · apply hright
        refine ⟨x + P, ⟨hcover _ hq ?_, ?_⟩, by ring⟩
        · exact ⟨by dsimp; linarith [hx.1], by dsimp; linarith [hx.2]⟩
        · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · have hdouble : (∫ x in (0 : ℝ)..2 * P, g x) =
        2 * ∫ x in (0 : ℝ)..P, g x := by
      simpa only [two_mul, zero_add] using
        hgp.intervalIntegral_add_eq_add 0 P (fun a b => hg.intervalIntegrable a b)
    calc
      (∫ x in E, f x) ≤ ∫ x in B, f x := hproj
      _ ≤ (τ * A) * ∫ x in (0 : ℝ)..2 * P, g x := hbound
      _ = (2 * τ * A) * ∫ x in (0 : ℝ)..P, g x := by rw [hdouble]; ring

end PoincareConjecture
