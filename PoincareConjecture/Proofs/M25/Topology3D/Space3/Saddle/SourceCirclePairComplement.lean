import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SourceCircleComplement
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp








set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Matrix

namespace PoincareConjecture.M25.Topology3D




theorem exists_source_circle_pair_complement
    (q : UnitCircle → UnitTwoSphere) (hq : Continuous q) (hqi : Injective q)
    (gamma : Fin 2 → unitInterval → UnitTwoSphere)
    (hg : ∀ i : Fin 2, Continuous (gamma i) ∧ Injective (gamma i))
    (hgd : Disjoint (range (gamma 0)) (range (gamma 1)))
    (hsub : ∀ i : Fin 2, range (gamma i) ⊆ range q)
    (p : Fin 4 → UnitTwoSphere)
    (hend : ∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2)))) :
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    ∃ (a v : Fin 2 → ℝ) (ends : Fin 2 × Fin 2 ≃ Fin 4) (eta : ℝ),
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    let V : Set UnitTwoSphere :=
      (gamma 0 '' Ioo (0 : unitInterval) 1) ∪ (gamma 1 '' Ioo (0 : unitInterval) 1)
    let C : Set UnitTwoSphere := range (gamma 0) ∪ range (gamma 1)
    0 < eta ∧ eta < 1 / 8 ∧
      (∀ k : Fin 2,
        0 < |v k| ∧ |v k| < 2 * Real.pi ∧ InjOn (alpha k) (Icc (-eta) (1 + eta)) ∧
        alpha k 0 = p (ends (k, 0)) ∧ alpha k 1 = p (ends (k, 1)) ∧
        Disjoint (alpha k '' Ioo (0 : ℝ) 1) C ∧
        (alpha k '' Icc (0 : ℝ) 1) ∩ C = {p (ends (k, 0)), p (ends (k, 1))} ∧
        (∀ t ∈ Ioo (-eta) (0 : ℝ), alpha k t ∈ V) ∧
        (∀ t ∈ Ioo (1 : ℝ) (1 + eta), alpha k t ∈ V)) ∧
      Disjoint (alpha 0 '' Icc (-eta) (1 + eta)) (alpha 1 '' Icc (-eta) (1 + eta)) ∧
      range q \ V = ⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1 ∧
      ∀ k : Fin 2, (ep.symm (ends (k, 0))).1 ≠ (ep.symm (ends (k, 1))).1 := by
  classical
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let V : Set UnitTwoSphere :=
    gamma 0 '' Ioo (0 : unitInterval) 1 ∪ gamma 1 '' Ioo (0 : unitInterval) 1
  let C : Set UnitTwoSphere := range (gamma 0) ∪ range (gamma 1)
  obtain ⟨a0, w, eta0, hw, hwpi, he0, he0lt, hP, hPi, hP0, hP1, hPo, hPc, htail0, htail1⟩ :=
    exists_source_circle_complement q hq hqi (gamma 0) (hg 0).1 (hg 0).2 (hsub 0)
  let P : ℝ → UnitTwoSphere := fun t => q (complexUnitCircleHomeomorph (Circle.exp (a0 + w * t)))
  change P 0 = gamma 0 0 at hP0
  change P 1 = gamma 0 1 at hP1
  have hI : Icc (0 : ℝ) 1 ⊆ Icc (-eta0) (1 + eta0) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hPcl : InjOn P (Icc (0 : ℝ) 1) := hPi.mono hI
  let P1 : unitInterval → UnitTwoSphere := fun t => P t
  have hP1c : Continuous P1 := hP.comp continuous_subtype_val
  have hP1i : Injective P1 := fun t s hts => Subtype.ext (hPcl t.property s.property hts)
  have hgrange (t : unitInterval) : gamma 1 t ∈ range P1 := by
    have ht : gamma 1 t ∈ P '' Ioo (0 : ℝ) 1 := by
      rw [← hPo]
      exact ⟨hsub 1 ⟨t, rfl⟩, fun hn => Set.disjoint_left.mp hgd hn ⟨t, rfl⟩⟩
    obtain ⟨s, hs, hst⟩ := ht
    exact ⟨⟨s, hs.1.le, hs.2.le⟩, hst⟩
  let e : unitInterval ≃ₜ range P1 := (hP1c.isClosedEmbedding hP1i).isEmbedding.toHomeomorph
  let z : unitInterval → ℝ := fun t => (e.symm ⟨gamma 1 t, hgrange t⟩ : ℝ)
  have hz : Continuous z := continuous_subtype_val.comp
    (e.symm.continuous.comp ((hg 1).1.subtype_mk _))
  have hrec (t : unitInterval) : P (z t) = gamma 1 t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨gamma 1 t, hgrange t⟩)
  have hzi : Injective z := by
    intro s t hst
    apply (hg 1).2
    rw [← hrec s, ← hrec t, hst]
  have hzb (t : unitInterval) : 0 < z t ∧ z t < 1 := by
    have ht := (e.symm ⟨gamma 1 t, hgrange t⟩).property
    have hz0 : z t ≠ 0 := by
      intro hz0
      have hh := hrec t
      rw [hz0, hP0] at hh
      exact Set.disjoint_left.mp hgd ⟨0, rfl⟩ ⟨t, hh.symm⟩
    have hz1 : z t ≠ 1 := by
      intro hz1
      have hh := hrec t
      rw [hz1, hP1] at hh
      exact Set.disjoint_left.mp hgd ⟨1, rfl⟩ ⟨t, hh.symm⟩
    exact ⟨lt_of_le_of_ne ht.1 hz0.symm, lt_of_le_of_ne ht.2 hz1⟩
  let Z : ℝ → ℝ := fun t => z (Set.projIcc 0 1 (by norm_num) t)
  have hZ : Continuous Z := hz.comp continuous_projIcc
  have hZval (t : unitInterval) : Z (t : ℝ) = z t := by simp only [Z, Set.projIcc_val]
  have hZi : InjOn Z (Icc (0 : ℝ) 1) := by
    intro t ht s hs hts
    have h := hzi (show z ⟨t, ht⟩ = z ⟨s, hs⟩ by
      simpa only [Z, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht,
        Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs] using hts)
    exact congrArg Subtype.val h
  let l : ℝ := min (z 0) (z 1)
  let r : ℝ := max (z 0) (z 1)
  have hne : z 0 ≠ z 1 := fun h => (by norm_num : (0 : unitInterval) ≠ 1) (hzi h)
  have hl : 0 < l := lt_min (hzb 0).1 (hzb 1).1
  have hr : r < 1 := max_lt (hzb 0).2 (hzb 1).2
  have hlr : l < r := min_lt_max.mpr hne
  have hl1 : l < 1 := hlr.trans hr
  have hr0 : 0 < r := hl.trans hlr
  have himages : Z '' Icc (0 : ℝ) 1 = Icc l r ∧ Z '' Ioo (0 : ℝ) 1 = Ioo l r := by
    have hZ0 : Z 0 = z 0 := hZval 0
    have hZ1 : Z 1 = z 1 := hZval 1
    by_cases ho : z 0 < z 1
    · have hm : StrictMonoOn Z (Icc (0 : ℝ) 1) :=
        hZ.continuousOn.strictMonoOn_of_injOn_Icc (by norm_num) (by rw [hZ0, hZ1]; exact ho.le) hZi
      exact ⟨by simpa only [hZ0, hZ1, l, r, min_eq_left ho.le, max_eq_right ho.le] using
          hZ.continuousOn.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn,
        by simpa only [hZ0, hZ1, l, r, min_eq_left ho.le, max_eq_right ho.le] using
          hZ.continuousOn.image_Ioo_of_strictMonoOn (by norm_num) hm⟩
    · have ho' : z 1 < z 0 := lt_of_le_of_ne (le_of_not_gt ho) hne.symm
      have hm : StrictAntiOn Z (Icc (0 : ℝ) 1) :=
        hZ.continuousOn.strictAntiOn_of_injOn_Icc (by norm_num) (by rw [hZ0, hZ1]; exact ho'.le) hZi
      exact ⟨by simpa only [hZ0, hZ1, l, r, min_eq_right ho'.le, max_eq_left ho'.le] using
          hZ.continuousOn.image_Icc_of_antitoneOn (by norm_num) hm.antitoneOn,
        by simpa only [hZ0, hZ1, l, r, min_eq_right ho'.le, max_eq_left ho'.le] using
          hZ.continuousOn.image_Ioo_of_strictAntiOn (by norm_num) hm⟩
  have hgammaC : range (gamma 1) = P '' Icc l r := by
    rw [← himages.1]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨z t, ⟨t, t.property, hZval t⟩, hrec t⟩
    · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa only [Z, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht] using
        (hrec ⟨t, ht⟩).symm
  have hgammaO : gamma 1 '' Ioo (0 : unitInterval) 1 = P '' Ioo l r := by
    rw [← himages.2]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨z t, ⟨t, ht, hZval t⟩, hrec t⟩
    · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨⟨t, ht.1.le, ht.2.le⟩, ht, ?_⟩
      simpa only [Z,
        Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ⟨ht.1.le, ht.2.le⟩] using
        (hrec ⟨t, ht.1.le, ht.2.le⟩).symm
  let base : Fin 2 → ℝ := ![0, r]
  let speed : Fin 2 → ℝ := ![l, 1 - r]
  let A : Fin 2 → ℝ := fun k => a0 + w * base k
  let W : Fin 2 → ℝ := fun k => w * speed k
  let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
    q (complexUnitCircleHomeomorph (Circle.exp (A k + W k * t)))
  let F : Fin 2 → ℝ → ℝ := fun k t => base k + speed k * t
  have hF0 (t : ℝ) : F 0 t = l * t := by simp [F, base, speed]
  have hF1 (t : ℝ) : F 1 t = r + (1 - r) * t := rfl
  have hspeed (k : Fin 2) : 0 < speed k ∧ speed k < 1 ∧ 0 ≤ base k ∧ base k + speed k ≤ 1 := by
    fin_cases k
    · change 0 < l ∧ l < 1 ∧ 0 ≤ (0 : ℝ) ∧ 0 + l ≤ 1
      exact ⟨hl, hl1, le_rfl, by linarith⟩
    · change 0 < 1 - r ∧ 1 - r < 1 ∧ 0 ≤ r ∧ r + (1 - r) ≤ 1
      exact ⟨by linarith, by linarith, hr0.le, by linarith⟩
  have hform (k : Fin 2) (t : ℝ) : alpha k t = P (F k t) := by
    change q (complexUnitCircleHomeomorph (Circle.exp (a0 + w * base k + w * speed k * t))) =
      q (complexUnitCircleHomeomorph (Circle.exp (a0 + w * (base k + speed k * t))))
    congr 3
    ring
  let eta : ℝ := min (eta0 / 2) ((r - l) / 4)
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  have het0 : eta < eta0 := (min_le_left _ _).trans_lt (by linarith)
  have hetgap : 2 * eta < r - l := by have := min_le_right (eta0 / 2) ((r - l) / 4); nlinarith
  have hmap (k : Fin 2) (t : ℝ) (ht : t ∈ Icc (-eta) (1 + eta)) : F k t ∈ Icc (-eta) (1 + eta) := by
    have hc := hspeed k
    have hlo := mul_le_mul_of_nonneg_left ht.1 hc.1.le
    have hhi := mul_le_mul_of_nonneg_left ht.2 hc.1.le
    have hm := mul_le_mul_of_nonneg_right hc.2.1.le heta.le
    dsimp [F]
    constructor <;> nlinarith [hc.2.2.1, hc.2.2.2]
  have hmap0 (k : Fin 2) (t : ℝ) (ht : t ∈ Icc (-eta) (1 + eta)) : F k t ∈ Icc (-eta0) (1 + eta0) :=
    ⟨by linarith [(hmap k t ht).1], by linarith [(hmap k t ht).2]⟩
  have hAi (k : Fin 2) : InjOn (alpha k) (Icc (-eta) (1 + eta)) := by
    intro t ht s hs heq
    rw [hform, hform] at heq
    have hh := hPi (hmap0 k t ht) (hmap0 k s hs) heq
    exact mul_left_cancel₀ (hspeed k).1.ne' (add_left_cancel hh)
  have hFopen (k : Fin 2) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      F k t ∈ Ioo (0 : ℝ) 1 ∧ (F k t < l ∨ r < F k t) := by
    fin_cases k
    · have hlo := mul_pos hl ht.1
      have hhi := mul_lt_mul_of_pos_left ht.2 hl
      change F 0 t ∈ Ioo (0 : ℝ) 1 ∧ (F 0 t < l ∨ r < F 0 t)
      rw [hF0]
      exact ⟨⟨hlo, by nlinarith⟩, Or.inl (by simpa using hhi)⟩
    · have hlo := mul_pos (sub_pos.mpr hr) ht.1
      have hhi := mul_lt_mul_of_pos_left ht.2 (sub_pos.mpr hr)
      change F 1 t ∈ Ioo (0 : ℝ) 1 ∧ (F 1 t < l ∨ r < F 1 t)
      rw [hF1]
      exact ⟨⟨by nlinarith, by nlinarith⟩, Or.inr (by nlinarith)⟩
  have havoid (k : Fin 2) : Disjoint (alpha k '' Ioo (0 : ℝ) 1) C := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ hy
    rw [hform] at hy
    have hf := hFopen k t ht
    rcases hy with hy | hy
    · have hh : P (F k t) ∈ range q \ range (gamma 0) := by
        rw [hPo]
        exact ⟨F k t, hf.1, rfl⟩
      exact hh.2 hy
    · rw [hgammaC] at hy
      obtain ⟨s, hs, heq⟩ := hy
      have hst := hPcl ⟨by linarith [hs.1], by linarith [hs.2]⟩
        ⟨hf.1.1.le, hf.1.2.le⟩ heq
      rcases hf.2 with hh | hh <;> linarith [hs.1, hs.2]
  have h00 : alpha 0 0 = gamma 0 0 := by rw [hform]; simpa [F, base, speed] using hP0
  have h01 : alpha 0 1 = P l := by rw [hform]; simp [F, base, speed]
  have h10 : alpha 1 0 = P r := by rw [hform]; simp [F, base, speed]
  have h11 : alpha 1 1 = gamma 0 1 := by rw [hform]; simpa [F, base, speed] using hP1
  let ends : Fin 2 × Fin 2 ≃ Fin 4 := ep.trans
    (if z 0 < z 1 then (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap 1 3) else Equiv.swap 1 3)
  have hends (k : Fin 2) : alpha k 0 = p (ends (k, 0)) ∧ alpha k 1 = p (ends (k, 1)) := by
    by_cases ho : z 0 < z 1
    · have hl' : l = z 0 := min_eq_left ho.le
      have hr' : r = z 1 := max_eq_right ho.le
      fin_cases k <;>
        simp only [ends, if_pos ho, Equiv.trans_apply, Equiv.swap_apply_def,
          ep, finProdFinEquiv] <;>
        norm_num <;> constructor
      · exact h00.trans (hend 0).1
      · exact h01.trans (by rw [hl', hrec]; exact (hend 1).1)
      · exact h10.trans (by rw [hr', hrec]; exact (hend 1).2)
      · exact h11.trans (hend 0).2
    · have ho' : z 1 < z 0 := lt_of_le_of_ne (le_of_not_gt ho) hne.symm
      have hl' : l = z 1 := min_eq_right ho'.le
      have hr' : r = z 0 := max_eq_left ho'.le
      fin_cases k <;>
        simp only [ends, if_neg ho, Equiv.trans_apply, Equiv.swap_apply_def,
          ep, finProdFinEquiv] <;>
        norm_num <;> constructor
      · exact h00.trans (hend 0).1
      · exact h01.trans (by rw [hl', hrec]; exact (hend 1).2)
      · exact h10.trans (by rw [hr', hrec]; exact (hend 1).1)
      · exact h11.trans (hend 0).2
  have hendC (k : Fin 2) : alpha k 0 ∈ C ∧ alpha k 1 ∈ C := by
    have hlC : P l ∈ range (gamma 1) := by rw [hgammaC]; exact ⟨l, ⟨le_rfl, hlr.le⟩, rfl⟩
    have hrC : P r ∈ range (gamma 1) := by rw [hgammaC]; exact ⟨r, ⟨hlr.le, le_rfl⟩, rfl⟩
    fin_cases k
    · exact ⟨Or.inl (h00.symm ▸ mem_range_self 0), Or.inr (h01.symm ▸ hlC)⟩
    · exact ⟨Or.inr (h10.symm ▸ hrC), Or.inl (h11.symm ▸ mem_range_self 1)⟩
  have hclosedC (k : Fin 2) :
      (alpha k '' Icc (0 : ℝ) 1) ∩ C = {p (ends (k, 0)), p (ends (k, 1))} := by
    rw [← (hends k).1, ← (hends k).2]
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hy⟩
      by_cases h0 : t = 0
      · exact Or.inl (congrArg (alpha k) h0)
      by_cases h1 : t = 1
      · exact Or.inr (congrArg (alpha k) h1)
      exact False.elim (Set.disjoint_left.mp (havoid k)
        ⟨t, ⟨lt_of_le_of_ne ht.1 (fun h => h0 h.symm), lt_of_le_of_ne ht.2 h1⟩, rfl⟩ hy)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by norm_num, rfl⟩, (hendC k).1⟩
      · exact ⟨⟨1, by norm_num, rfl⟩, (hendC k).2⟩
  have htail (k : Fin 2) :
      (∀ t ∈ Ioo (-eta) (0 : ℝ), alpha k t ∈ V) ∧
      (∀ t ∈ Ioo (1 : ℝ) (1 + eta), alpha k t ∈ V) := by
    constructor <;> intro t ht
    · have htc : t ∈ Icc (-eta) (1 + eta) := ⟨ht.1.le, by linarith [ht.2]⟩
      rw [hform]
      fin_cases k
      · apply Or.inl
        apply htail0
        have hh := hmap 0 t htc
        change -eta0 < F 0 t ∧ F 0 t < 0
        rw [hF0] at hh ⊢
        exact ⟨by linarith [hh.1], mul_neg_of_pos_of_neg hl ht.2⟩
      · apply Or.inr
        rw [hgammaO]
        have hb := mul_lt_mul_of_pos_left ht.1 (sub_pos.mpr hr)
        have hn := mul_neg_of_pos_of_neg (sub_pos.mpr hr) ht.2
        have he := mul_le_mul_of_nonneg_right (show 1 - r ≤ 1 by linarith) heta.le
        refine ⟨F 1 t, ?_, rfl⟩
        change l < r + (1 - r) * t ∧ r + (1 - r) * t < r
        constructor <;> nlinarith
    · have htc : t ∈ Icc (-eta) (1 + eta) := ⟨by linarith [ht.1], ht.2.le⟩
      rw [hform]
      fin_cases k
      · apply Or.inr
        rw [hgammaO]
        have hb := mul_lt_mul_of_pos_left ht.1 hl
        have hu := mul_lt_mul_of_pos_left ht.2 hl
        have he := mul_le_mul_of_nonneg_right hl1.le heta.le
        refine ⟨F 0 t, ?_, rfl⟩
        rw [hF0]
        change l < l * t ∧ l * t < r
        constructor <;> nlinarith
      · apply Or.inl
        apply htail1
        have hh := hmap 1 t htc
        have hb := mul_lt_mul_of_pos_left ht.1 (sub_pos.mpr hr)
        change 1 < F 1 t ∧ F 1 t < 1 + eta0
        rw [hF1] at hh ⊢
        exact ⟨by nlinarith, by linarith [hh.2]⟩
  have hdis : Disjoint (alpha 0 '' Icc (-eta) (1 + eta)) (alpha 1 '' Icc (-eta) (1 + eta)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ ⟨s, hs, hst⟩
    rw [hform, hform] at hst
    have heq := hPi (hmap0 1 s hs) (hmap0 0 t ht) hst
    rw [hF1, hF0] at heq
    have hleft := mul_le_mul_of_nonneg_left ht.2 hl.le
    have hright := mul_le_mul_of_nonneg_left hs.1 (sub_nonneg.mpr hr.le)
    have hle := mul_le_mul_of_nonneg_right hl1.le heta.le
    have hre := mul_le_mul_of_nonneg_right (show 1 - r ≤ 1 by linarith) heta.le
    nlinarith
  have himg (b d : ℝ) (hd : 0 < d) :
      (fun t : ℝ => P (b + d * t)) '' Icc (0 : ℝ) 1 = P '' Icc b (b + d) := by
    have hm : StrictMono (fun t : ℝ => b + d * t) := fun x y hxy =>
      add_lt_add_right (mul_lt_mul_of_pos_left hxy hd) b
    have hc : Continuous (fun t : ℝ => b + d * t) :=
      continuous_const.add (continuous_const.mul continuous_id)
    have hi := hc.continuousOn.image_Icc_of_monotoneOn
      (a := (0 : ℝ)) (b := 1) (by norm_num) (hm.monotone.monotoneOn _)
    change (P ∘ fun t : ℝ => b + d * t) '' Icc (0 : ℝ) 1 = _
    rw [image_comp, hi]
    simp only [mul_zero, add_zero, mul_one]
  have him0 : alpha 0 '' Icc (0 : ℝ) 1 = P '' Icc 0 l := by
    have hh : alpha 0 = fun t : ℝ => P (0 + l * t) := funext (hform 0)
    rw [hh, himg 0 l hl, zero_add]
  have him1 : alpha 1 '' Icc (0 : ℝ) 1 = P '' Icc r 1 := by
    have hh : alpha 1 = fun t : ℝ => P (r + (1 - r) * t) := funext (hform 1)
    rw [hh, himg r (1 - r) (sub_pos.mpr hr)]
    congr 2
    ring
  have hsplit : Icc (0 : ℝ) 1 \ Ioo l r = Icc 0 l ∪ Icc r 1 := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      by_cases htl : t ≤ l
      · exact Or.inl ⟨ht.1, htl⟩
      · exact Or.inr ⟨le_of_not_gt (fun htr => hn ⟨lt_of_not_ge htl, htr⟩), ht.2⟩
    · rintro (ht | ht)
      · exact ⟨⟨ht.1, ht.2.trans hl1.le⟩, fun hh => (not_lt_of_ge ht.2) hh.1⟩
      · exact ⟨⟨hr0.le.trans ht.1, ht.2⟩, fun hh => (not_lt_of_ge ht.1) hh.2⟩
  have hcover : range q \ V = ⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1 := by
    have hdiff : range q \ V = (range q \ (gamma 0 '' Ioo (0 : unitInterval) 1)) \
        (gamma 1 '' Ioo (0 : unitInterval) 1) := by
      ext y
      simp only [V, mem_sdiff, mem_union]
      tauto
    rw [hdiff, hPc, hgammaO, ← hPcl.image_sdiff_subset
      (show Ioo l r ⊆ Icc (0 : ℝ) 1 from fun t ht => ⟨hl.le.trans ht.1.le, ht.2.le.trans hr.le⟩),
      hsplit, image_union, ← him0, ← him1]
    ext y
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (hy | hy)
      · exact ⟨0, hy⟩
      · exact ⟨1, hy⟩
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
  refine ⟨A, W, ends, eta, heta, het0.trans he0lt, ?_, hdis, hcover, ?_⟩
  · intro k
    have hs := hspeed k
    have hv : |W k| = |w| * speed k := by simp only [W, abs_mul, abs_of_pos hs.1]
    have hvm : |w| * speed k < |w| := by simpa using mul_lt_mul_of_pos_left hs.2.1 hw
    exact ⟨hv.symm ▸ mul_pos hw hs.1, hv.symm ▸ hvm.trans hwpi, hAi k,
      (hends k).1, (hends k).2, havoid k, hclosedC k, (htail k).1, (htail k).2⟩
  · intro k
    by_cases ho : z 0 < z 1 <;> fin_cases k <;>
      norm_num [ends, ho, ep, finProdFinEquiv, Equiv.swap_apply_def]
    all_goals decide

end PoincareConjecture.M25.Topology3D
