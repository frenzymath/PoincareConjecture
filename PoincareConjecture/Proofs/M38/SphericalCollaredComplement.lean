import PoincareConjecture.Proofs.M38.SphericalRegionComplement
import PoincareConjecture.Proofs.M38.CollaredRegionComplement

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_spherical_collared_region_complement
    {ι : Type*} [Finite ι] {U : Set sphereCarrier.{u}.carrier}
    (hU : IsOpen U) (hconnected : IsConnected U)
    (f : ι → UnitTwoSphere → sphereCarrier.{u}.carrier)
    (hf : ∀ i, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (f i)) (range (f j)))
    (hfrontier : frontier U = ⋃ i, range (f i))
    (c : ι → OpenPartialHomeomorph RoundCylinderSpace sphereCarrier.{u}.carrier)
    (hc : ∀ i, ContMDiffOn CylModel (𝓡 3) ∞ (c i) (c i).source)
    (hci : ∀ i, ContMDiffOn (𝓡 3) CylModel ∞ (c i).symm (c i).target)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (hsource : ∀ i, univ ×ˢ Ioo (-δ i) (δ i) ⊆ (c i).source)
    (hzero : ∀ i z, c i (z, 0) = f i z)
    (hpositive : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < δ i →
      c i (z, s) ∈ U) :
    ∃ B : ι → SurgeryBallEmbedding sphereCarrier.{u}, ∃ r : ι → ℝ,
      (∀ i, 0 < r i ∧ r i < 1 / 2) ∧
      (∀ i, frontier (B i).closedBall = range (f i)) ∧
      (∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall) ∧
      U = (⋃ i, (B i).closedBall)ᶜ ∧
      ∀ i (z : UnitTwoSphere) (s : ℝ), |s| < r i →
        (B i).map ((1 + s) • z.val) = c i (z, s) := by
  obtain ⟨B, hBfront, hBsep, hUB⟩ :=
    exists_spherical_region_complement hU hconnected f hf hdisjoint hfrontier
  have hzero' (i) : c i '' (univ ×ˢ ({0} : Set ℝ)) = frontier (B i).closedBall := by
    rw [hBfront]
    ext y
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      have hs0 : s = 0 := hs
      subst s
      exact ⟨z, (hzero i z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z, 0), by simp, hzero i z⟩
  obtain ⟨D, r, hr, hDB, hDsep, hUD, hmatch⟩ :=
    exists_collared_region_complement B hBsep hUB c hc hci δ hδ hsource hzero' hpositive
  exact ⟨D, r, hr, fun i => by rw [hDB, hBfront], hDsep, hUD, hmatch⟩

end PoincareConjecture.M38
