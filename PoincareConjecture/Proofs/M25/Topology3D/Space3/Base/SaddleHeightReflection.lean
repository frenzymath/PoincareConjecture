import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.CapHeightReflection











set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem SaddlePieceData.reverseHeight_spec
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData psi u) :
    let D' : SaddlePieceData psi (-u) := D.reverseHeight
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let f' : UnitTwoSphere → ℝ :=
      fun q => ⟪((-u : UnitTwoSphere) : E3), psi (q, 0)⟫_ℝ
    D'.capCount = D.capCount ∧
    D'.sourceCore = D.sourceCore ∧
    D'.point = D.point ∧
    D'.morse = D.morse ∧
    D'.protectedSet = D.protectedSet ∧
    D'.cutRadius = D.cutRadius ∧
    D'.slabLower = -D.slabUpper ∧
    D'.slabUpper = -D.slabLower ∧
    D'.morseSign1 = -D.morseSign1 ∧
    D'.morseSign2 = -D.morseSign2 ∧
    (∀ i : Fin D.capCount, D'.cap i = (D.cap i).reverseHeight) ∧
    f' = -f ∧
    (∀ q : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f' q =
        -mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q) ∧
    (∀ q : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f' q = 0 ↔
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0) ∧
    (∀ t : ℝ,
      {q : UnitTwoSphere | f' q = t} =
        {q : UnitTwoSphere | f q = -t}) ∧
    (∀ t : ℝ,
      D'.sourceCore ∩ {q : UnitTwoSphere | f' q ≤ t} =
        D.sourceCore ∩ {q : UnitTwoSphere | -t ≤ f q}) := by
  dsimp only
  obtain ⟨hcount, hcore, hpoint, hmorse, hprotected, hradius, hlower, hupper,
    hsign1, hsign2, hcap⟩ := D.reverseHeight_geometry
  have hf : (fun q : UnitTwoSphere => ⟪((-u : UnitTwoSphere) : E3), psi (q, 0)⟫_ℝ) =
      -(fun q : UnitTwoSphere => ⟪(u : E3), psi (q, 0)⟫_ℝ) := by
    funext q
    simp only [Pi.neg_apply, coe_neg_sphere, inner_neg_left]
  have hd : ∀ q : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪((-u : UnitTwoSphere) : E3), psi (p, 0)⟫_ℝ) q =
        -mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q := by
    intro q
    rw [hf, mfderiv_neg]
  refine ⟨hcount, hcore, hpoint, hmorse, hprotected, hradius, hlower, hupper,
    hsign1, hsign2, hcap, hf, hd, ?_, ?_, ?_⟩
  · intro q
    rw [hd q]
    exact neg_eq_zero
  · intro t
    ext q
    simp only [mem_ofPred_eq, coe_neg_sphere, inner_neg_left]
    constructor <;> intro h <;> linarith
  · intro t
    ext q
    change (q ∈ D.sourceCore ∧ ⟪((-u : UnitTwoSphere) : E3), psi (q, 0)⟫_ℝ ≤ t) ↔
      (q ∈ D.sourceCore ∧ -t ≤ ⟪(u : E3), psi (q, 0)⟫_ℝ)
    rw [coe_neg_sphere, inner_neg_left]
    constructor <;> rintro ⟨hq, ht⟩ <;> exact ⟨hq, by linarith⟩

end PoincareConjecture.M25.Topology3D
