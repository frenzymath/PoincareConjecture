import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection










set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




noncomputable def heightPreservingSliceDiffeomorph
    (u : UnitTwoSphere) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ)
    (z : ℝ) : D2 := by
  let L := heightPlaneCoordinates u
  let f : E2 → E2 := fun x => (L (K (L.symm (x, z)))).1
  let g : E2 → E2 := fun x => (L (K.symm (L.symm (x, z)))).1
  have hKi (y : E3) : ⟪(u : E3), K.symm y⟫_ℝ = ⟪(u : E3), y⟫_ℝ := by
    simpa only [Diffeomorph.apply_symm_apply] using (hK (K.symm y)).symm
  have hh (y : E3) : (L (K y)).2 = (L y).2 := by
    simpa only [L, heightPlaneCoordinates_snd] using hK y
  have hhi (y : E3) : (L (K.symm y)).2 = (L y).2 := by
    simpa only [L, heightPlaneCoordinates_snd] using hKi y
  have hf : ContDiff ℝ ∞ f := contDiff_fst.comp
    (L.contDiff.comp (K.contMDiff_toFun.contDiff.comp
      (L.symm.contDiff.comp (contDiff_id.prodMk contDiff_const))))
  have hg : ContDiff ℝ ∞ g := contDiff_fst.comp
    (L.contDiff.comp (K.contMDiff_invFun.contDiff.comp
      (L.symm.contDiff.comp (contDiff_id.prodMk contDiff_const))))
  exact {
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := by
        intro x
        have hp : (f x, z) = L (K (L.symm (x, z))) := Prod.ext rfl
          ((hh (L.symm (x, z))).trans (congrArg Prod.snd (L.apply_symm_apply (x, z)))).symm
        change (L (K.symm (L.symm (f x, z)))).1 = x
        rw [hp, L.symm_apply_apply, K.symm_apply_apply, L.apply_symm_apply]
      right_inv := by
        intro x
        have hp : (g x, z) = L (K.symm (L.symm (x, z))) := Prod.ext rfl
          ((hhi (L.symm (x, z))).trans (congrArg Prod.snd (L.apply_symm_apply (x, z)))).symm
        change (L (K (L.symm (g x, z)))).1 = x
        rw [hp, L.symm_apply_apply, K.apply_symm_apply, L.apply_symm_apply] }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hg.contMDiff }



theorem heightPreservingSliceDiffeomorph_geometry
    (u : UnitTwoSphere) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    let L := heightPlaneCoordinates u
    let F := heightPreservingSliceDiffeomorph u K hK
    (∀ y : E3, ⟪(u : E3), K.symm y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) ∧
    (∀ z : ℝ, ∀ x : E2, F z x = (L (K (L.symm (x, z)))).1) ∧
    (∀ z : ℝ, ∀ x : E2, (F z).symm x = (L (K.symm (L.symm (x, z)))).1) ∧
    (∀ z : ℝ, ∀ x : E2, K (L.symm (x, z)) = L.symm (F z x, z)) ∧
    (∀ z : ℝ, ∀ x : E2, K.symm (L.symm (x, z)) = L.symm ((F z).symm x, z)) ∧
    ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1) ∧
    ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1) ∧
    (∀ z : ℝ,
      (F z).toHomeomorph.toOpenPartialHomeomorph.source = (univ : Set E2) ∧
      (F z).toHomeomorph.toOpenPartialHomeomorph.target = (univ : Set E2)) := by
  let L := heightPlaneCoordinates u
  let F := heightPreservingSliceDiffeomorph u K hK
  have hKi (y : E3) : ⟪(u : E3), K.symm y⟫_ℝ = ⟪(u : E3), y⟫_ℝ := by
    simpa only [Diffeomorph.apply_symm_apply] using (hK (K.symm y)).symm
  have hheight (z : ℝ) (x : E2) : (L (K (L.symm (x, z)))).2 = z := by
    rw [show (L (K (L.symm (x, z)))).2 = (L (L.symm (x, z))).2 from
      by simpa only [L, heightPlaneCoordinates_snd] using hK (L.symm (x, z)),
      L.apply_symm_apply]
  have hheighti (z : ℝ) (x : E2) : (L (K.symm (L.symm (x, z)))).2 = z := by
    rw [show (L (K.symm (L.symm (x, z)))).2 = (L (L.symm (x, z))).2 from
      by simpa only [L, heightPlaneCoordinates_snd] using hKi (L.symm (x, z)),
      L.apply_symm_apply]
  refine ⟨hKi, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, fun _ => ⟨rfl, rfl⟩⟩
  · intro z x
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl (hheight z x)
  · intro z x
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl (hheighti z x)
  · exact contDiff_fst.comp (L.contDiff.comp (K.contMDiff_toFun.contDiff.comp L.symm.contDiff))
  · exact contDiff_fst.comp (L.contDiff.comp (K.contMDiff_invFun.contDiff.comp L.symm.contDiff))

end PoincareConjecture.M25.Topology3D
