import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcFrontierGerm













noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture




theorem m64Intrinsic_loop_injOn_Ioc
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T)) :
    InjOn gamma (Ioc 0 T) := by
  intro x hx y hy hxy
  by_cases hxT : x = T
  · by_cases hyT : y = T
    · exact hxT.trans hyT.symm
    · have hyI : y ∈ Ico 0 T := ⟨hy.1.le, lt_of_le_of_ne hy.2 hyT⟩
      have heq := hinj ⟨le_rfl, hT⟩ hyI (hend.trans (hxT ▸ hxy))
      exact False.elim (hy.1.ne' heq.symm)
  · by_cases hyT : y = T
    · have hxI : x ∈ Ico 0 T := ⟨hx.1.le, lt_of_le_of_ne hx.2 hxT⟩
      have heq := hinj hxI ⟨le_rfl, hT⟩ ((hyT ▸ hxy).trans hend.symm)
      exact False.elim (hx.1.ne' heq)
    · exact hinj ⟨hx.1.le, lt_of_le_of_ne hx.2 hxT⟩
        ⟨hy.1.le, lt_of_le_of_ne hy.2 hyT⟩ hxy





theorem m64Intrinsic_loop_corner_decomposition
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T)) :
    ∃ (a : ℝ) (W : Set AnnulusCoordinates),
      0 < a ∧ InjOn gamma (Icc 0 a) ∧
      InjOn (fun s => gamma (T - s)) (Icc 0 a) ∧
      IsCompact W ∧ gamma 0 ∉ W ∧
      gamma '' Icc 0 T = gamma '' Icc 0 a ∪
        (fun s => gamma (T - s)) '' Icc 0 a ∪ W := by
  let a := T / 4
  have ha : 0 < a := by dsimp only [a]; positivity
  have haT : a < T := by dsimp only [a]; linarith
  have hleft : InjOn gamma (Icc 0 a) := by
    intro s hs t ht heq
    exact hinj ⟨hs.1, hs.2.trans_lt haT⟩ ⟨ht.1, ht.2.trans_lt haT⟩ heq
  have hright : InjOn (fun s => gamma (T - s)) (Icc 0 a) := by
    intro s hs t ht heq
    have h := m64Intrinsic_loop_injOn_Ioc hT hend hinj
      (show T - s ∈ Ioc 0 T by constructor <;> linarith [hs.1, hs.2])
      (show T - t ∈ Ioc 0 T by constructor <;> linarith [ht.1, ht.2]) heq
    linarith
  let W := gamma '' Icc a (T - a)
  have hpW : gamma 0 ∉ W := by
    rintro ⟨t, ht, heq⟩
    have h := hinj (show t ∈ Ico 0 T by constructor <;> linarith [ht.1, ht.2])
      ⟨le_rfl, hT⟩ heq
    linarith [ht.1]
  refine ⟨a, W, ha, hleft, hright, isCompact_Icc.image hg, hpW, ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases hta : t ≤ a
    · exact Or.inl (Or.inl ⟨t, ⟨ht.1, hta⟩, rfl⟩)
    by_cases hat : T - a ≤ t
    · exact Or.inl (Or.inr ⟨T - t, ⟨by linarith [ht.2], by linarith⟩, by
        change gamma (T - (T - t)) = gamma t
        rw [sub_sub_cancel]⟩)
    · exact Or.inr ⟨t, ⟨(lt_of_not_ge hta).le, (lt_of_not_ge hat).le⟩, rfl⟩
  · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact ⟨t, ⟨ht.1, ht.2.trans haT.le⟩, rfl⟩
    · exact ⟨T - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · exact ⟨t, ⟨ha.le.trans ht.1, by linarith [ht.2]⟩, rfl⟩

end PoincareConjecture
