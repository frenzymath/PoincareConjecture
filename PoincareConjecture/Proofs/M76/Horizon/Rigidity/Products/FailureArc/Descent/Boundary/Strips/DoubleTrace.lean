import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private def oldSheet (i : Bool) (p : P2) : C3 :=
  ((p.2, if i then -p.2 else p.2), p.1)

private theorem oldSheet_mem (i : Bool) {p : P2} (hp : p ∈ source) : oldSheet i p ∈ tube := by
  cases i
  · exact ⟨⟨hp.2, hp.2⟩, hp.1⟩
  · refine ⟨⟨hp.2, ?_⟩, hp.1⟩
    change -1 ≤ -p.2 ∧ -p.2 ≤ 1
    constructor <;> linarith [hp.2.1, hp.2.2]

theorem original_strip_double_trace
    {A X : Type*} {S : Set A} {f : A → X} {τ : C3 → X}
    (c : Bool → P2 → A) (hcS : ∀ i, MapsTo (c i) source S)
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : S ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source) (i : Bool) :
    (c i '' source) ∩ doubleLocusOn f S = c i '' arm 0 := by
  have hsheet (k : Bool) (p : P2) (hp : p ∈ source) : f (c k p) = τ (oldSheet k p) := by
    cases k
    · exact h0 p hp
    · exact h1 p hp
  apply Subset.antisymm
  · rintro x ⟨⟨p, hp, rfl⟩, _, y, hy, hxy, hne⟩
    have hyU : y ∈ f ⁻¹' (τ '' tube) :=
      ⟨oldSheet i p, oldSheet_mem i hp, (hsheet i p hp).symm.trans hxy⟩
    have hyc : ∃ (k : Bool) (q : P2), q ∈ source ∧ c k q = y := by
      rcases hfull.subset ⟨hy, hyU⟩ with ⟨q, hq, he⟩ | ⟨q, hq, he⟩
      · exact ⟨false, q, hq, he⟩
      · exact ⟨true, q, hq, he⟩
    obtain ⟨k, q, hq, rfl⟩ := hyc
    have he : oldSheet i p = oldSheet k q := hτ (oldSheet_mem i hp) (oldSheet_mem k hq)
      ((hsheet i p hp).symm.trans (hxy.trans (hsheet k q hq)))
    have ht := congrArg Prod.snd he
    have hx := congrArg (fun z : C3 ↦ z.1.1) he
    have hv := congrArg (fun z : C3 ↦ z.1.2) he
    change p.1 = q.1 at ht
    change p.2 = q.2 at hx
    have hp0 : p.2 = 0 := by
      cases i <;> cases k
      · exact (hne (congrArg (c false) (Prod.ext ht hx))).elim
      · change p.2 = -q.2 at hv
        linarith
      · change -p.2 = q.2 at hv
        linarith
      · exact (hne (congrArg (c true) (Prod.ext ht hx))).elim
    exact ⟨p, ⟨hp.1, hp0⟩, rfl⟩
  · rintro x ⟨p, hp, rfl⟩
    have hpS : p ∈ source := ⟨hp.1, by rw [hp.2]; norm_num⟩
    refine ⟨⟨p, hpS, rfl⟩, hcS i hpS, c (!i) p, hcS (!i) hpS, ?_, ?_⟩
    · rw [hsheet i p hpS, hsheet (!i) p hpS]
      congr 1
      have hp0 : p.2 = 0 := hp.2
      cases i <;> simp [oldSheet, hp0]
    · intro he
      cases i
      · exact disjoint_left.mp hdis ⟨p, hpS, rfl⟩ ⟨p, hpS, he.symm⟩
      · exact disjoint_left.mp hdis ⟨p, hpS, he.symm⟩ ⟨p, hpS, rfl⟩

end PoincareConjecture.M76.Dehn
