import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

local notation "I01" => Icc (0 : ℝ) 1
local notation "I12" => Icc (1 : ℝ) 2



theorem isFinitePLBallPair_joined_intervals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U V : Set E} {a b c : E} (p : I01 ≃ₜ U) (q : I01 ≃ₜ V)
    (hp : p.IsFinitePL) (hq : q.IsFinitePL)
    (hp0 : (p (0 : unitInterval) : E) = a) (hp1 : (p (1 : unitInterval) : E) = b)
    (hq0 : (q (0 : unitInterval) : E) = b) (hq1 : (q (1 : unitInterval) : E) = c)
    (hUV : U ∩ V = {b}) : IsFinitePLBallPair ℝ (U ∪ V) {a, c} := by
  obtain ⟨r, hr, hr0, hr1⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).exists_unitInterval_chart_with_endpoints
      (show (0 : ℝ) ≠ 1 by norm_num)
  obtain ⟨s, hs, hs0, hs1⟩ :=
    (isFinitePLBallPair_Icc (show (1 : ℝ) < 2 by norm_num)).exists_unitInterval_chart_with_endpoints
      (show (1 : ℝ) ≠ 2 by norm_num)
  change (r (0 : unitInterval) : ℝ) = 0 at hr0
  change (r (1 : unitInterval) : ℝ) = 1 at hr1
  change (s (0 : unitInterval) : ℝ) = 1 at hs0
  change (s (1 : unitInterval) : ℝ) = 2 at hs1
  let e := p.symm.trans r
  let f := q.symm.trans s
  have hmodel : I01 ∩ I12 = ({1} : Set ℝ) := by
    ext x
    constructor
    · intro hx
      exact le_antisymm hx.1.2 hx.2.1
    · rintro rfl
      norm_num
  have hoverlap (x : U) : (x : E) ∈ V ↔ (e x : ℝ) ∈ I12 := by
    obtain ⟨t, rfl⟩ := p.surjective x
    have hleft : (p t : E) ∈ V ↔ t = 1 := by
      have hmem : (p t : E) ∈ V ↔ (p t : E) = b := by
        rw [← mem_singleton_iff, ← hUV]
        simp only [mem_inter_iff, (p t).property, true_and]
      rw [hmem, ← hp1]
      exact Subtype.coe_injective.eq_iff.trans p.injective.eq_iff
    have hright : (r t : ℝ) ∈ I12 ↔ t = 1 := by
      have hmem : (r t : ℝ) ∈ I12 ↔ (r t : ℝ) = 1 := by
        rw [← mem_singleton_iff, ← hmodel]
        simp only [mem_inter_iff, (r t).property, true_and]
      rw [hmem]
      exact ⟨fun h ↦ r.injective (Subtype.ext (h.trans hr1.symm)), fun h ↦ h ▸ hr1⟩
    simpa only [e, Homeomorph.trans_apply, p.symm_apply_apply] using hleft.trans hright.symm
  have hagree (x : E) (hxU : x ∈ U) (hxV : x ∈ V) :
      (e ⟨x, hxU⟩ : ℝ) = f ⟨x, hxV⟩ := by
    have hx : x = b := hUV.subset ⟨hxU, hxV⟩
    have hpX : (⟨x, hxU⟩ : U) = p 1 := Subtype.ext (hx.trans hp1.symm)
    have hqX : (⟨x, hxV⟩ : V) = q 0 := Subtype.ext (hx.trans hq0.symm)
    simp only [hpX, hqX, e, f, Homeomorph.trans_apply, p.symm_apply_apply,
      q.symm_apply_apply, hr1, hs0]
  obtain ⟨H, hH, hHU, hHV⟩ := Homeomorph.exists_union_finitePL e f
    (hp.symm.trans hr) (hq.symm.trans hs) hoverlap hagree
  have hcover : I01 ∪ I12 = Icc (0 : ℝ) 2 := Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
  have hmodelBall : IsFinitePLBallPair ℝ (I01 ∪ I12) {(0 : ℝ), 2} := by
    rw [hcover]
    exact isFinitePLBallPair_Icc (by norm_num)
  have haU : a ∈ U := hp0 ▸ (p 0).property
  have hcV : c ∈ V := hq1 ▸ (q 1).property
  have hHa : (H ⟨a, Or.inl haU⟩ : ℝ) = 0 := by
    have h := hHU (p 0)
    simpa only [hp0, e, Homeomorph.trans_apply, p.symm_apply_apply, hr0] using h
  have hHc : (H ⟨c, Or.inr hcV⟩ : ℝ) = 2 := by
    have h := hHV (q 1)
    simpa only [hq1, f, Homeomorph.trans_apply, q.symm_apply_apply, hs1] using h
  apply hmodelBall.of_homeomorph (by
    rintro x (rfl | hx)
    · exact Or.inl haU
    · exact Or.inr (mem_singleton_iff.mp hx ▸ hcV)) H hH
  intro x
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (hx | hx)
    · left
      have heq : x = ⟨a, Or.inl haU⟩ := Subtype.ext hx
      rw [heq]
      exact hHa
    · right
      have heq : x = ⟨c, Or.inr hcV⟩ := Subtype.ext hx
      rw [heq]
      exact hHc
  · rintro (hx | hx)
    · exact Or.inl (congrArg Subtype.val (H.injective (Subtype.ext (hx.trans hHa.symm))))
    · exact Or.inr (congrArg Subtype.val (H.injective (Subtype.ext (hx.trans hHc.symm))))

end PoincareConjecture.M76.Dehn
