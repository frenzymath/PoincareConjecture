import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarFamilyHeightLift

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_nonnested_height_lift_image
    (Phi : ℝ → D2)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hzero : ∀ x : E2, Phi 0 x = x)
    (C : Set E2) (hC : IsCompact C)
    (hfix : ∀ t : ℝ, ∀ x : E2, x ∉ C → Phi t x = x)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hsChi : HasCompactSupport chi) (u : UnitTwoSphere)
    (sourceSlice targetSlice : ℝ → Set E2)
    (himage : ∀ z : ℝ, Phi (chi z) '' sourceSlice z = targetSlice z) :
    let L := heightPlaneCoordinates u
    let sourceStack : Set (E2 × ℝ) :=
      ⋃ z : ℝ, sourceSlice z ×ˢ ({z} : Set ℝ)
    let targetStack : Set (E2 × ℝ) :=
      ⋃ z : ℝ, targetSlice z ×ˢ ({z} : Set ℝ)
    ∃ G : D3,
      (∀ x : E2, ∀ z : ℝ,
        G (L.symm (x, z)) = L.symm (Phi (chi z) x, z) ∧
        G.symm (L.symm (x, z)) = L.symm ((Phi (chi z)).symm x, z)) ∧
      IsCompact (L.symm '' (C ×ˢ tsupport chi)) ∧
      tsupport (fun y : E3 => G y - y) ⊆ L.symm '' (C ×ˢ tsupport chi) ∧
      tsupport (fun y : E3 => G.symm y - y) ⊆ L.symm '' (C ×ˢ tsupport chi) ∧
      G '' (L.symm '' sourceStack) = L.symm '' targetStack ∧
      G.symm '' (L.symm '' targetStack) = L.symm '' sourceStack := by
  dsimp only
  let L := heightPlaneCoordinates u
  let sourceStack : Set (E2 × ℝ) :=
    ⋃ z : ℝ, sourceSlice z ×ˢ ({z} : Set ℝ)
  let targetStack : Set (E2 × ℝ) :=
    ⋃ z : ℝ, targetSlice z ×ˢ ({z} : Set ℝ)
  obtain ⟨G, hformula, hcompact, hsupport, hsupportInv⟩ :=
    exists_compact_planar_family_height_lift Phi hPhi hzero C hC hfix chi hchi hsChi u
  have hforward : G '' (L.symm '' sourceStack) = L.symm '' targetStack := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ sourceSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      refine ⟨(Phi (chi z) x, z), ?_, (hformula x z).1.symm⟩
      refine mem_iUnion.mpr ⟨z, ⟨?_, rfl⟩⟩
      rw [← himage z]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ targetSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      have hxi : (Phi (chi z)).symm x ∈ sourceSlice z := by
        have hx' : x ∈ (Phi (chi z)) '' sourceSlice z := by
          rw [himage z]
          exact hx
        rcases hx' with ⟨y, hy, hyx⟩
        rw [← hyx]
        simpa only [(Phi (chi z)).symm_apply_apply] using hy
      refine ⟨L.symm ((Phi (chi z)).symm x, z), ?_, ?_⟩
      · refine ⟨((Phi (chi z)).symm x, z), ?_, rfl⟩
        exact mem_iUnion.mpr ⟨z, ⟨hxi, rfl⟩⟩
      · rw [(hformula ((Phi (chi z)).symm x) z).1]
        simp only [(Phi (chi z)).apply_symm_apply]
        rfl
  have hinverse : G.symm '' (L.symm '' targetStack) = L.symm '' sourceStack := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ targetSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      have hxi : (Phi (chi z)).symm x ∈ sourceSlice z := by
        have hx' : x ∈ (Phi (chi z)) '' sourceSlice z := by
          rw [himage z]
          exact hx
        rcases hx' with ⟨y, hy, hyx⟩
        rw [← hyx]
        simpa only [(Phi (chi z)).symm_apply_apply] using hy
      refine ⟨((Phi (chi z)).symm x, z), ?_, (hformula x z).2.symm⟩
      · exact mem_iUnion.mpr ⟨z, ⟨hxi, rfl⟩⟩
    · rintro ⟨p, hp, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ sourceSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      refine ⟨L.symm (Phi (chi z) x, z), ?_, ?_⟩
      · refine ⟨(Phi (chi z) x, z), ?_, rfl⟩
        refine mem_iUnion.mpr ⟨z, ⟨?_, rfl⟩⟩
        rw [← himage z]
        exact ⟨x, hx, rfl⟩
      · rw [(hformula (Phi (chi z) x) z).2]
        simp only [(Phi (chi z)).symm_apply_apply]
        rfl
  exact ⟨G, hformula, hcompact, hsupport, hsupportInv, hforward, hinverse⟩

end PoincareConjecture.M25.Topology3D
