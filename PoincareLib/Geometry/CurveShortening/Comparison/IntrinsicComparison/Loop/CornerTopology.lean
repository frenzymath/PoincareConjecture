import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Arc.FrontierGerm

/-!
# The two actual arcs at a simple return-loop junction

The half-open injectivity of the simple loop also gives injectivity on the
opposite half-open interval. Two short endpoint arcs and the compact middle
then supply the exact boundary decomposition at the return point.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481. These project
Jordan-region constructions supply the actual domains, boundary charts and finite
faces used in its regional Gauss--Bonnet arguments.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT

/-- A simple loop is injective on either half-open choice of its period. Source:
`proof-work/tasks/M64/reports/2026-09-24-intrinsic-radial-scalar.md`, Actual return-loop
corner caps. -/
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

/-- Two actual short arcs at the return point are compact embedded arcs. Their remaining
compact middle is disjoint from the junction itself. Source:
`proof-work/tasks/M64/reports/2026-09-24-intrinsic-radial-scalar.md`, Actual return-loop
corner caps. -/
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

end PoincareMT
