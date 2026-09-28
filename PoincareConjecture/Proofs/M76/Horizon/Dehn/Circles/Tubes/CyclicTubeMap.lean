import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PrismCycle
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicFrames

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)

theorem exists_signed_cyclic_tube_of_incident_frames
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (t : Fin (n + 4) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 3) → Set E) (J : Fin (n + 2) → Set E)
    (G : ∀ e, signedTubeDiamond ≃ₜ J e) (hG : ∀ e, (G e).IsFinitePL)
    (map : ∀ i, ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (left right : Fin (n + 2) → Fin 2 → Bool) (first last initial : Fin 2 → Bool)
    (hcontact : ∀ e : Fin (n + 2), B e.castSucc ∩ B e.succ = J e)
    (hupper : ∀ (e : Fin (n + 2)) (x : signedTubeDiamond),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) =
          G e (signedTubeDiamondReflection (left e) x))
    (hlower : ∀ (e : Fin (n + 2)) (x : signedTubeDiamond),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) =
          G e (signedTubeDiamondReflection (right e) x))
    (Jclose : Set E) (Gclose : signedTubeDiamond ≃ₜ Jclose)
    (hclose : B 0 ∩ B (Fin.last (n + 2)) = Jclose)
    (hfirst : ∀ x : signedTubeDiamond,
      (map 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by change (0 : ℕ) < 1; omega)).le⟩ : E) =
          Gclose (signedTubeDiamondReflection first x))
    (hlast : ∀ x : signedTubeDiamond,
      (map (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) =
          Gclose (signedTubeDiamondReflection last x))
    (hfar : ∀ i j : Fin (n + 3), i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = Fin.last (n + 2)) → Disjoint (B i) (B j)) :
    ∃ (frame : Fin (n + 3) → Fin 2 → Bool) (closing : Fin 2 → Bool) (τ : P2 × ℝ → E),
      frame 0 = initial ∧
      closing = signedCycleClosingFrame first last (frame 0) (frame (Fin.last (n + 2))) ∧
      FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))) ∧
      (∀ i (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ))),
        τ x = map i (signedTubePrismReparametrization
          (signedTubeDiamondReflection (frame i)) (t i.castSucc) (t i.succ) x)) ∧
      τ '' (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))) = ⋃ i, B i ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))),
        τ x = τ y ↔ x = y ∨
          ((x : P2 × ℝ).2 = t 0 ∧ (y : P2 × ℝ).2 = t (Fin.last (n + 3)) ∧
            signedTubeReflection closing (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
          ((y : P2 × ℝ).2 = t 0 ∧ (x : P2 × ℝ).2 = t (Fin.last (n + 3)) ∧
            signedTubeReflection closing (y : P2 × ℝ).1 = (x : P2 × ℝ).1) := by
  obtain ⟨frame, closing, h0, hframe, hclosing, hclosingValue⟩ :=
    exists_signed_cycle_frames n left right first last initial
  let maps := fun i ↦ (signedTubePrismReparametrization
    (signedTubeDiamondReflection (frame i)) (t i.castSucc) (t i.succ)).trans (map i)
  have hmaps (i) : (maps i).IsFinitePL :=
    (signedTubePrismReparametrization_isFinitePL
      (signedTubeDiamondReflection_isFinitePL (hG 0) (frame i)) (ht Fin.castSucc_lt_succ)).trans
        (hmap i)
  let joint := fun e ↦ ((signedTubeDiamondReflection (frame e.castSucc)).trans
    (signedTubeDiamondReflection (left e))).trans (G e)
  have hu (e) (x : signedTubeDiamond) :
      (maps e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = joint e x :=
    hupper e (signedTubeDiamondReflection (frame e.castSucc) x)
  have hl (e) (x : signedTubeDiamond) :
      (maps e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = joint e x := by
    exact (hlower e (signedTubeDiamondReflection (frame e.succ) x)).trans
      (congrArg Subtype.val (signedTubeDiamondReflection_incident_agreement
        (G e) (left e) (right e) (frame e.castSucc) (frame e.succ) (hframe e) x)).symm
  let closeJoint := ((signedTubeDiamondReflection (frame (Fin.last (n + 2)))).trans
    (signedTubeDiamondReflection last)).trans Gclose
  have hfirst' (x : signedTubeDiamond) :
      (maps 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by change (0 : ℕ) < 1; omega)).le⟩ : E) =
          closeJoint (signedTubeDiamondReflection closing x) := by
    exact (hfirst (signedTubeDiamondReflection (frame 0) x)).trans
      (congrArg (fun z : signedTubeDiamond ↦ (Gclose z : E)) (hclosingValue x)).symm
  have hlast' (x : signedTubeDiamond) :
      (maps (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = closeJoint x :=
    hlast (signedTubeDiamondReflection (frame (Fin.last (n + 2))) x)
  obtain ⟨τ, hτ, hval, himage, hfib⟩ := exists_signed_prism_cycle_map t ht B J joint maps
    hmaps hcontact hu hl Jclose closeJoint (signedTubeDiamondReflection closing)
      hclose hfirst' hlast' hfar
  exact ⟨frame, closing, τ, h0, hclosing, hτ, hval, himage, hfib⟩

end PoincareConjecture.M76.Dehn
