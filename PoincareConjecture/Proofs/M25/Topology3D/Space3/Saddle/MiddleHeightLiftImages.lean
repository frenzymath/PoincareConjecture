import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarFamilyHeightLift

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_saddle_middle_height_lift_images
    (u : UnitTwoSphere)
    (Phi : ℝ → D2)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hzero : ∀ x : E2, Phi 0 x = x)
    (C : Set E2) (hC : IsCompact C)
    (hfix : ∀ t : ℝ, ∀ x : E2, x ∉ C → Phi t x = x)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hsChi : HasCompactSupport chi)
    (S : ℝ → Set E2)
    (hS : ∀ z : ℝ,
      Phi (chi z) '' S z = S z ∧
      (Phi (chi z)).symm '' S z = S z) :
    ∃ (G : D3) (K : Set E3),
      (∀ x : E2, ∀ z : ℝ,
        G ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm (Phi (chi z) x, z) ∧
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((Phi (chi z)).symm x, z)) ∧
      IsCompact K ∧
      tsupport (fun y : E3 => G y - y) ⊆ K ∧
      tsupport (fun y : E3 => G.symm y - y) ⊆ K ∧
      (∀ z : ℝ,
        G '' ((heightPlaneCoordinates u).symm '' (S z ×ˢ ({z} : Set ℝ))) =
          (heightPlaneCoordinates u).symm '' (S z ×ˢ ({z} : Set ℝ)) ∧
        G.symm '' ((heightPlaneCoordinates u).symm '' (S z ×ˢ ({z} : Set ℝ))) =
          (heightPlaneCoordinates u).symm '' (S z ×ˢ ({z} : Set ℝ))) := by
  let L := heightPlaneCoordinates u
  obtain ⟨G, hformula, hK, hsupport, hsupporti⟩ :=
    exists_compact_planar_family_height_lift Phi hPhi hzero C hC hfix
      chi hchi hsChi u
  refine ⟨G, _, hformula, hK, hsupport, hsupporti, ?_⟩
  intro z
  have hforward :
      G '' (L.symm '' (S z ×ˢ ({z} : Set ℝ))) =
        L.symm '' (S z ×ˢ ({z} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, t⟩
      have ht : t = z := by simpa using hp.2
      subst t
      have hout : Phi (chi z) x ∈ S z := by
        rw [← (hS z).1]
        exact ⟨x, hp.1, rfl⟩
      refine ⟨(Phi (chi z) x, z), ⟨hout, rfl⟩, ?_⟩
      exact (hformula x z).1.symm
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, t⟩
      have ht : t = z := by simpa using hp.2
      subst t
      have hin : (Phi (chi z)).symm x ∈ S z := by
        rw [← (hS z).2]
        exact ⟨x, hp.1, rfl⟩
      refine ⟨L.symm ((Phi (chi z)).symm x, z),
        ⟨((Phi (chi z)).symm x, z), ⟨hin, rfl⟩, rfl⟩, ?_⟩
      simpa only [L, (Phi (chi z)).apply_symm_apply] using
        (hformula ((Phi (chi z)).symm x) z).1
  have hinverse :
      G.symm '' (L.symm '' (S z ×ˢ ({z} : Set ℝ))) =
        L.symm '' (S z ×ˢ ({z} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, t⟩
      have ht : t = z := by simpa using hp.2
      subst t
      have hin : (Phi (chi z)).symm x ∈ S z := by
        rw [← (hS z).2]
        exact ⟨x, hp.1, rfl⟩
      refine ⟨((Phi (chi z)).symm x, z), ⟨hin, rfl⟩, ?_⟩
      simpa only [L] using (hformula x z).2.symm
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, t⟩
      have ht : t = z := by simpa using hp.2
      subst t
      have hout : Phi (chi z) x ∈ S z := by
        rw [← (hS z).1]
        exact ⟨x, hp.1, rfl⟩
      refine ⟨L.symm (Phi (chi z) x, z),
        ⟨(Phi (chi z) x, z), ⟨hout, rfl⟩, rfl⟩, ?_⟩
      simpa only [L, (Phi (chi z)).symm_apply_apply] using
        (hformula (Phi (chi z) x) z).2
  exact ⟨hforward, hinverse⟩

end PoincareConjecture.M25.Topology3D
