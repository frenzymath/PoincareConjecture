import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Coordinates.Cylinder
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Corner.PlanarLift

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1

theorem exists_normalized_rim_lift
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    {K : Set A} (H : Rim ≃ₜ Rim) (hH : H.IsFinitePL)
    {q : A → E} (hq : FinitePiecewiseAffineOn q K) (hqi : InjOn q K)
    (hmap : MapsTo q K (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ∃ q' : A → E, FinitePiecewiseAffineOn q' K ∧ InjOn q' K ∧
      MapsTo q' K (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      ∀ p (hp : p ∈ K), q' p =
        ((H.symm ⟨(q p).1, (hmap hp).1⟩ : V2), (q p).2) := by
  let C := rimCylinderReparam H
  have hC : C.IsFinitePL := rimCylinderReparam_finitePL hH
  obtain ⟨k, hk, hkeq⟩ := hC.symm
  have hmem (p) (hp : p ∈ K) : q p ∈ rimCylinder :=
    ⟨(hmap hp).1, (hmap hp).2.1.le, (hmap hp).2.2.le⟩
  have heq (p) (hp : p ∈ K) : k (q p) =
      ((H.symm ⟨(q p).1, (hmap hp).1⟩ : V2), (q p).2) :=
    (hkeq ⟨q p, hmem p hp⟩).symm
  refine ⟨k ∘ q, hk.comp hq hmem, ?_, ?_, heq⟩
  · intro p hp z hz h
    apply hqi hp hz
    have h' : C.symm ⟨q p, hmem p hp⟩ = C.symm ⟨q z, hmem z hz⟩ := by
      apply Subtype.ext
      exact (hkeq ⟨q p, hmem p hp⟩).trans
        (h.trans (hkeq ⟨q z, hmem z hz⟩).symm)
    exact congrArg Subtype.val (C.symm.injective h')
  · intro p hp
    change k (q p) ∈ _
    rw [heq p hp]
    exact ⟨(H.symm _).property, (hmap hp).2⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
