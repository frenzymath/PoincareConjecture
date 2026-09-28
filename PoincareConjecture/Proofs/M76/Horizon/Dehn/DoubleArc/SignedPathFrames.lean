import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondReflection









set_option autoImplicit false

namespace PoincareConjecture.M76.Dehn

theorem signedTubeReindex_assoc (a b c : Bool) :
    signedTubeReindex a (signedTubeReindex b c) =
      signedTubeReindex (signedTubeReindex a b) c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem signedTubeReindex_comm (a b : Bool) :
    signedTubeReindex a b = signedTubeReindex b a := by
  cases a <;> cases b <;> rfl

theorem signedTubeReflection_comp (a b : Fin 2 → Bool) (x : ℝ × ℝ) :
    signedTubeReflection a (signedTubeReflection b x) =
      signedTubeReflection (fun i => signedTubeReindex (a i) (b i)) x := by
  ext
  · cases ha : a 0 <;> cases hb : b 0 <;>
      simp [signedTubeReflection_apply, signedTubeReindex, ha, hb]
  · cases ha : a 1 <;> cases hb : b 1 <;>
      simp [signedTubeReflection_apply, signedTubeReindex, ha, hb]

theorem signedTubeDiamondReflection_comp (a b : Fin 2 → Bool) (x : signedTubeDiamond) :
    signedTubeDiamondReflection a (signedTubeDiamondReflection b x) =
      signedTubeDiamondReflection (fun i => signedTubeReindex (a i) (b i)) x :=
  Subtype.ext (signedTubeReflection_comp a b x)



theorem signedTubeDiamondReflection_incident_agreement
    {E : Type*} [TopologicalSpace E] {J : Set E}
    (G : signedTubeDiamond ≃ₜ J) (left right frameLeft frameRight : Fin 2 → Bool)
    (h : ∀ i, signedTubeReindex (left i) (frameLeft i) =
      signedTubeReindex (right i) (frameRight i)) (x : signedTubeDiamond) :
    G (signedTubeDiamondReflection left (signedTubeDiamondReflection frameLeft x)) =
      G (signedTubeDiamondReflection right (signedTubeDiamondReflection frameRight x)) := by
  rw [signedTubeDiamondReflection_comp, signedTubeDiamondReflection_comp]
  rw [funext h]



theorem exists_signed_path_frames (n : ℕ)
    (left right : Fin (n + 1) → Fin 2 → Bool) (initial : Fin 2 → Bool) :
    ∃ frame : Fin (n + 2) → Fin 2 → Bool,
      frame 0 = initial ∧ ∀ (e : Fin (n + 1)) (i : Fin 2),
        signedTubeReindex (left e i) (frame e.castSucc i) =
          signedTubeReindex (right e i) (frame e.succ i) := by
  let f : ℕ → Fin 2 → Bool := Nat.rec initial (fun k prev =>
    if hk : k < n + 1 then fun i =>
      signedTubeReindex (right ⟨k, hk⟩ i) (signedTubeReindex (left ⟨k, hk⟩ i) (prev i))
    else prev)
  let frame : Fin (n + 2) → Fin 2 → Bool := fun v => f v.val
  refine ⟨frame, rfl, ?_⟩
  intro e i
  have he : e.val < n + 1 := e.isLt
  change signedTubeReindex (left e i) (f e.val i) =
    signedTubeReindex (right e i) (f (e.val + 1) i)
  simp only [f, Nat.rec_add_one, dif_pos he]
  exact (signedTubeReindex_involutive (right e i) _).symm

end PoincareConjecture.M76.Dehn
