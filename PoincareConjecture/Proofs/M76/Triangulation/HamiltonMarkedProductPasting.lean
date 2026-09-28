import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedProductHalves
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_joined_marked_product_map {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b) (F fp fn : (V2 × ℝ) → E)
    {w : ℝ} (hw : 0 < w)
    (hpp : FinitePiecewiseAffineOn fp (D2 ×ˢ Icc 0 w))
    (hnp : FinitePiecewiseAffineOn fn (D2 ×ˢ Icc 0 w))
    (hpi : InjOn fp (D2 ×ˢ Icc 0 w)) (hni : InjOn fn (D2 ×ˢ Icc 0 w))
    (hpm : MapsTo fp (D2 ×ˢ Icc 0 w) (P.map '' (D2 ×ˢ Icc (0 : ℝ) 1)))
    (hnm : MapsTo fn (D2 ×ˢ Icc 0 w) (P.map '' (D2 ×ˢ Icc (-1 : ℝ) 0)))
    (hpc : ∀ x : D2, fp ((x : V2), 0) = b x)
    (hnc : ∀ x : D2, fn ((x : V2), 0) = b x)
    (hpb : ∀ p ∈ D2 ×ˢ Icc 0 w, fp p ∈ frontier R ↔ p.1 ∈ Q2)
    (hnb : ∀ p ∈ D2 ×ˢ Icc 0 w, fn p ∈ frontier R ↔ p.1 ∈ Q2)
    (hpl : ∀ x ∈ Q2, ∀ t ∈ Icc 0 w, fp (x, t) = F (x, t))
    (hnl : ∀ x ∈ Q2, ∀ t ∈ Icc 0 w, fn (x, t) = F (x, -t)) :
    ∃ g : (V2 × ℝ) → E,
      FinitePiecewiseAffineOn g (D2 ×ˢ Icc (-w) w) ∧
      InjOn g (D2 ×ˢ Icc (-w) w) ∧ MapsTo g (D2 ×ˢ Icc (-w) w) R ∧
      (∀ p ∈ D2 ×ˢ Icc (-w) w, g p ∈ frontier R ↔ p.1 ∈ Q2) ∧
      (∀ x ∈ Q2, ∀ t ∈ Icc (-w) w, g (x, t) = F (x, t)) ∧
      ∀ x : D2, g ((x : V2), 0) = b x := by
  classical
  let A := D2 ×ˢ Icc (0 : ℝ) w
  let N := D2 ×ˢ Icc (-w) (0 : ℝ)
  let U := D2 ×ˢ Icc (-w) w
  have hreflect : diskTimeReflection.symm '' A = N := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change q.1 ∈ D2 ∧ -q.2 ∈ Icc (-w) 0
      exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
    · intro hp
      refine ⟨(p.1, -p.2), ⟨hp.1, ?_⟩, ?_⟩
      · constructor <;> linarith [hp.2.1, hp.2.2]
      · change (p.1, - -p.2) = p
        simp only [neg_neg, Prod.eta]
  have hnt : FinitePiecewiseAffineOn (fn ∘ diskTimeReflection) N := by
    have h := hnp.precomp_affineEquiv diskTimeReflection.toContinuousAffineEquiv
    change FinitePiecewiseAffineOn (fn ∘ diskTimeReflection) (diskTimeReflection.symm '' A) at h
    rwa [hreflect] at h
  have hneg (p : V2 × ℝ) (hp : p ∈ N) : diskTimeReflection p ∈ A :=
    ⟨hp.1, by change -p.2 ∈ Icc 0 w; constructor <;> linarith [hp.2.1, hp.2.2]⟩
  let g : (V2 × ℝ) → E := fun p => if 0 ≤ p.2 then fp p else fn (diskTimeReflection p)
  have hgp (p : V2 × ℝ) (hp : p ∈ A) : g p = fp p := if_pos hp.2.1
  have hgn (p : V2 × ℝ) (hp : p ∈ N) : g p = fn (diskTimeReflection p) := by
    by_cases ht : 0 ≤ p.2
    · have he : p.2 = 0 := le_antisymm hp.2.2 ht
      have hpe : p = (p.1, (0 : ℝ)) := Prod.ext rfl he
      rw [hpe]
      change (if 0 ≤ (0 : ℝ) then fp (p.1, 0) else fn (diskTimeReflection (p.1, 0))) =
        fn (p.1, -(0 : ℝ))
      rw [if_pos le_rfl, neg_zero, hpc ⟨p.1, hp.1⟩, hnc ⟨p.1, hp.1⟩]
    · exact if_neg ht
  have hcover : A ∪ N = U := by
    ext p
    constructor
    · rintro (hp | hp)
      · exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
      · exact ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩
    · intro hp
      by_cases ht : 0 ≤ p.2
      · exact Or.inl ⟨hp.1, ht, hp.2.2⟩
      · exact Or.inr ⟨hp.1, hp.2.1, le_of_not_ge ht⟩
  have hgPL : FinitePiecewiseAffineOn g U := by
    rw [← hcover]
    exact finitePiecewiseAffineOn_union (hpp.congr (fun p hp => (hgp p hp).symm))
      (hnt.congr (fun p hp => (hgn p hp).symm))
  have hcross (p q : V2 × ℝ) (hp : p ∈ A) (hq : q ∈ A) (he : fp p = fn q) :
      p.2 = 0 ∧ q.2 = 0 := by
    have hyD : fp p ∈ D := P.half_images_inter ▸
      And.intro (hpm hp) (he.symm ▸ hnm hq)
    let x := b.symm ⟨fp p, hyD⟩
    have hx : (b x : E) = fp p := congrArg Subtype.val (b.apply_symm_apply _)
    have hxA : ((x : V2), (0 : ℝ)) ∈ A := ⟨x.property, le_rfl, hw.le⟩
    have hp0 := hpi hp hxA ((hpc x).trans hx).symm
    have hq0 := hni hq hxA (he.symm.trans ((hpc x).trans hx).symm |>.trans
      ((hpc x).trans (hnc x).symm))
    exact ⟨congrArg Prod.snd hp0, congrArg Prod.snd hq0⟩
  refine ⟨g, hgPL, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq he
    by_cases hpt : 0 ≤ p.2 <;> by_cases hqt : 0 ≤ q.2
    · exact hpi ⟨hp.1, hpt, hp.2.2⟩ ⟨hq.1, hqt, hq.2.2⟩
        ((hgp p ⟨hp.1, hpt, hp.2.2⟩).symm.trans
          (he.trans (hgp q ⟨hq.1, hqt, hq.2.2⟩)))
    · have hqN : q ∈ N := ⟨hq.1, hq.2.1, le_of_not_ge hqt⟩
      have hppA : p ∈ A := ⟨hp.1, hpt, hp.2.2⟩
      rw [hgp p hppA, hgn q hqN] at he
      have hz := (hcross p _ hppA (hneg q hqN) he).2
      change -q.2 = 0 at hz
      exact False.elim (hqt (by linarith))
    · have hpN : p ∈ N := ⟨hp.1, hp.2.1, le_of_not_ge hpt⟩
      have hqqA : q ∈ A := ⟨hq.1, hqt, hq.2.2⟩
      rw [hgn p hpN, hgp q hqqA] at he
      have hz := (hcross q _ hqqA (hneg p hpN) he.symm).2
      change -p.2 = 0 at hz
      exact False.elim (hpt (by linarith))
    · have hpN : p ∈ N := ⟨hp.1, hp.2.1, le_of_not_ge hpt⟩
      have hqN : q ∈ N := ⟨hq.1, hq.2.1, le_of_not_ge hqt⟩
      rw [hgn p hpN, hgn q hqN] at he
      exact diskTimeReflection.injective (hni (hneg p hpN) (hneg q hqN) he)
  · intro p hp
    by_cases ht : 0 ≤ p.2
    · have hpA : p ∈ A := ⟨hp.1, ht, hp.2.2⟩
      rw [hgp p hpA]
      obtain ⟨z, hz, he⟩ := hpm hpA
      exact he ▸ P.inside ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    · have hpN : p ∈ N := ⟨hp.1, hp.2.1, le_of_not_ge ht⟩
      rw [hgn p hpN]
      obtain ⟨z, hz, he⟩ := hnm (hneg p hpN)
      exact he ▸ P.inside ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  · intro p hp
    by_cases ht : 0 ≤ p.2
    · have hpA : p ∈ A := ⟨hp.1, ht, hp.2.2⟩
      rw [hgp p hpA]
      exact hpb p hpA
    · have hpN : p ∈ N := ⟨hp.1, hp.2.1, le_of_not_ge ht⟩
      rw [hgn p hpN]
      exact hnb _ (hneg p hpN)
  · intro x hx t ht
    by_cases ht0 : 0 ≤ t
    · rw [hgp (x, t) ⟨sphere_subset_closedBall hx, ht0, ht.2⟩]
      exact hpl x hx t ⟨ht0, ht.2⟩
    · rw [hgn (x, t) ⟨sphere_subset_closedBall hx, ht.1, le_of_not_ge ht0⟩]
      change fn (x, -t) = F (x, t)
      rw [hnl x hx (-t) ⟨by linarith, by linarith [ht.1]⟩, neg_neg]
  · intro x
    exact (hgp ((x : V2), 0) ⟨x.property, le_rfl, hw.le⟩).trans (hpc x)

end PoincareConjecture.M76.HamiltonIndexOne
