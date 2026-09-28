import PoincareConjecture.Proofs.M76.Rigidity.MatchedCollarMap

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X : Type*} [TopologicalSpace X]
  {L : Set E} {K : Set F} {R : Set X}
  {Q : E → F} {c : E × ℝ → X} {d : F × ℝ → X}

theorem matchedCollarMap_side_marks (hR : IsClosed R)
    (hQ : MapsTo Q L K)
    (hcR : MapsTo c (L ×ˢ Icc (0 : ℝ) 1) R)
    (hdT : MapsTo d (K ×ˢ Icc (0 : ℝ) 1) (interior R)ᶜ)
    (hcfront : ∀ z ∈ L ×ˢ Icc (0 : ℝ) 1, c z ∈ frontier R ↔ z.2 = 0)
    (hdfront : ∀ z ∈ K ×ˢ Icc (0 : ℝ) 1, d z ∈ frontier R ↔ z.2 = 0)
    (z : E × ℝ) (hz : z ∈ L ×ˢ Icc (-1 : ℝ) 1) :
    (matchedCollarMap Q c d z ∈ frontier R ↔ z.2 = 0) ∧
      (matchedCollarMap Q c d z ∈ R ↔ 0 ≤ z.2) ∧
      (matchedCollarMap Q c d z ∈ (interior R)ᶜ ↔ z.2 ≤ 0) := by
  by_cases ht : 0 ≤ z.2
  · rw [matchedCollarMap_nonneg Q c d ht]
    have hzp : z ∈ L ×ˢ Icc (0 : ℝ) 1 := ⟨hz.1, ht, hz.2.2⟩
    refine ⟨hcfront z hzp, ⟨fun _ => ht, fun _ => hcR hzp⟩, ?_⟩
    constructor
    · intro hminus
      have hf : c z ∈ frontier R := by
        rw [hR.frontier_eq]
        exact ⟨hcR hzp, hminus⟩
      exact ((hcfront z hzp).mp hf).le
    · intro hle
      have hf := (hcfront z hzp).mpr (le_antisymm hle ht)
      rw [hR.frontier_eq] at hf
      exact hf.2
  · simp only [matchedCollarMap, if_neg ht]
    have htime : z.2 < 0 := lt_of_not_ge ht
    have hwn : (Q z.1, -z.2) ∈ K ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hQ hz.1, by linarith, by linarith [hz.2.1]⟩
    have hfnot : d (Q z.1, -z.2) ∉ frontier R := by
      intro hf
      have hzero := (hdfront (Q z.1, -z.2) hwn).mp hf
      dsimp at hzero
      linarith
    have hrnot : d (Q z.1, -z.2) ∉ R := by
      intro hr
      apply hfnot
      rw [hR.frontier_eq]
      exact ⟨hr, hdT hwn⟩
    refine ⟨⟨fun hf => False.elim (hfnot hf), ?_⟩,
      ⟨fun hr => False.elim (hrnot hr), fun hle => False.elim (ht hle)⟩,
      ⟨fun _ => htime.le, fun _ => hdT hwn⟩⟩
    intro hzero
    exact False.elim (ht (hzero ▸ le_rfl))

theorem injOn_matchedCollarMap (hR : IsClosed R)
    (hQ : MapsTo Q L K) (hQi : InjOn Q L)
    (hci : InjOn c (L ×ˢ Icc (0 : ℝ) 1))
    (hdi : InjOn d (K ×ˢ Icc (0 : ℝ) 1))
    (hcR : MapsTo c (L ×ˢ Icc (0 : ℝ) 1) R)
    (hdT : MapsTo d (K ×ˢ Icc (0 : ℝ) 1) (interior R)ᶜ)
    (hcfront : ∀ z ∈ L ×ˢ Icc (0 : ℝ) 1, c z ∈ frontier R ↔ z.2 = 0)
    (hdfront : ∀ z ∈ K ×ˢ Icc (0 : ℝ) 1, d z ∈ frontier R ↔ z.2 = 0) :
    InjOn (matchedCollarMap Q c d) (L ×ˢ Icc (-1 : ℝ) 1) := by
  have hside (z : E × ℝ) (hz : z ∈ L ×ˢ Icc (-1 : ℝ) 1) :=
    (matchedCollarMap_side_marks hR hQ hcR hdT hcfront hdfront z hz).2.1
  intro z hz w hw hzw
  by_cases hz0 : 0 ≤ z.2
  · have hw0 : 0 ≤ w.2 := (hside w hw).mp (hzw ▸ (hside z hz).mpr hz0)
    rw [matchedCollarMap_nonneg Q c d hz0, matchedCollarMap_nonneg Q c d hw0] at hzw
    exact hci ⟨hz.1, hz0, hz.2.2⟩ ⟨hw.1, hw0, hw.2.2⟩ hzw
  · have hw0 : ¬0 ≤ w.2 := by
      intro hw0
      apply hz0
      exact (hside z hz).mp (hzw.symm ▸ (hside w hw).mpr hw0)
    simp only [matchedCollarMap, if_neg hz0, if_neg hw0] at hzw
    have hzminus : (Q z.1, -z.2) ∈ K ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hQ hz.1, by linarith [lt_of_not_ge hz0], by linarith [hz.2.1]⟩
    have hwminus : (Q w.1, -w.2) ∈ K ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hQ hw.1, by linarith [lt_of_not_ge hw0], by linarith [hw.2.1]⟩
    have heq : (Q z.1, -z.2) = (Q w.1, -w.2) := hdi hzminus hwminus hzw
    have hbase : Q z.1 = Q w.1 := congrArg Prod.fst heq
    have htime : -z.2 = -w.2 := congrArg Prod.snd heq
    exact Prod.ext (hQi hz.1 hw.1 hbase) (neg_injective htime)

end Geometry
