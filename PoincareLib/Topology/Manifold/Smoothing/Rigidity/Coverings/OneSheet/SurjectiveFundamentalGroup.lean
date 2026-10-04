import Mathlib.Topology.Homotopy.Lifting

/-!
# One-sheet coverings from surjectivity on based loops

Path lifting makes the based fiber a transitive monodromy set. Surjectivity
of the actual induced fundamental-group homomorphism makes this action
fix the chosen lift, so every fiber is a singleton.
-/

noncomputable section

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (hp : IsCoveringMap p)

set_option backward.isDefEq.respectTransparency.types false in
/-- Surjectivity on based loops collapses the fiber over the chosen basepoint. -/
theorem eq_basepoint_of_fundamentalGroup_map_surjective [PathConnectedSpace E]
    (e : E) (hsurj : Function.Surjective (FundamentalGroup.map ⟨p, hp.continuous⟩ e))
    {y : E} (hy : p y = p e) : y = e := by
  let Γ : Path.Homotopic.Quotient e y := .mk (PathConnectedSpace.somePath e y)
  let γ : FundamentalGroup X (p e) := (Γ.map ⟨p, hp.continuous⟩).cast rfl hy.symm
  have hΓ : hp.monodromy γ ⟨e, rfl⟩ = ⟨y, hy⟩ := by
    apply hp.monodromy_eq_of_map_eq Γ
    dsimp [γ]
    rw [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
  obtain ⟨δ, hδ⟩ := hsurj γ
  have hδ' : Path.Homotopic.Quotient.map δ ⟨p, hp.continuous⟩ = γ := hδ
  rw [← hδ', hp.monodromy_map] at hΓ
  exact (congrArg Subtype.val hΓ).symm

/-- A path-connected covering with surjective induced based fundamental-group
map is bijective over a path-connected base. -/
theorem bijective_of_fundamentalGroup_map_surjective
    [PathConnectedSpace E] [PathConnectedSpace X]
    (e : E) (hsurj : Function.Surjective (FundamentalGroup.map ⟨p, hp.continuous⟩ e)) :
    Function.Bijective p := by
  have hfiber : Subsingleton (p ⁻¹' {p e}) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    exact (hp.eq_basepoint_of_fundamentalGroup_map_surjective e hsurj a.2).trans
      (hp.eq_basepoint_of_fundamentalGroup_map_surjective e hsurj b.2).symm
  constructor
  · intro a b hab
    let γ : Path.Homotopic.Quotient (p a) (p e) :=
      .mk (PathConnectedSpace.somePath (p a) (p e))
    have h := (hp.monodromy_bijective γ).1
      (hfiber.elim (hp.monodromy γ ⟨a, rfl⟩) (hp.monodromy γ ⟨b, hab.symm⟩))
    exact congrArg Subtype.val h
  · intro x
    let γ : Path.Homotopic.Quotient (p e) x :=
      .mk (PathConnectedSpace.somePath (p e) x)
    exact ⟨(hp.monodromy γ ⟨e, rfl⟩).1, (hp.monodromy γ ⟨e, rfl⟩).2⟩

/-- The homeomorphism carried by a one-sheet covering. Its forward map is
definitionally the original covering map. -/
def homeomorphOfFundamentalGroupMapSurjective
    [PathConnectedSpace E] [PathConnectedSpace X]
    (e : E) (hsurj : Function.Surjective (FundamentalGroup.map ⟨p, hp.continuous⟩ e)) :
    E ≃ₜ X :=
  hp.isLocalHomeomorph.toHomeomorphOfBijective
    (hp.bijective_of_fundamentalGroup_map_surjective e hsurj)

@[simp] theorem homeomorphOfFundamentalGroupMapSurjective_apply
    [PathConnectedSpace E] [PathConnectedSpace X]
    (e : E) (hsurj : Function.Surjective (FundamentalGroup.map ⟨p, hp.continuous⟩ e))
    (y : E) : hp.homeomorphOfFundamentalGroupMapSurjective e hsurj y = p y := rfl

end IsCoveringMap
