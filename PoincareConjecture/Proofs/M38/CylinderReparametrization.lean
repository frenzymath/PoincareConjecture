import PoincareConjecture.Proofs.M38.CylinderRegionTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (G : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
  RoundCylinderSpace RoundCylinderSpace ∞)
  (hG : G '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) = Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)

include hG


theorem cylinderReparametrization_mem {p : RoundCylinderSpace}
    (hp : p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    G p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := hG.subset ⟨p, hp, rfl⟩


theorem cylinderReparametrization_symm_mem {p : RoundCylinderSpace}
    (hp : p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    G.symm p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨q, hq, hqp⟩ := hG.symm.subset hp
  rw [← hqp, G.symm_apply_apply]
  exact hq


noncomputable def cylinderStripHomeomorph :
    (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) ≃ₜ (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) where
  toFun z := ((G (z.1, z.2.val)).1,
    ⟨(G (z.1, z.2.val)).2,
      (cylinderReparametrization_mem G hG ⟨Set.mem_univ _, z.2.property⟩).2⟩)
  invFun z := ((G.symm (z.1, z.2.val)).1,
    ⟨(G.symm (z.1, z.2.val)).2,
      (cylinderReparametrization_symm_mem G hG ⟨Set.mem_univ _, z.2.property⟩).2⟩)
  left_inv z := by
    apply Prod.ext
    · change (G.symm (G (z.1, z.2.val))).1 = z.1
      exact congrArg (fun p : RoundCylinderSpace => p.1) (G.symm_apply_apply (z.1, z.2.val))
    · apply Subtype.ext
      change (G.symm (G (z.1, z.2.val))).2 = z.2.val
      exact congrArg (fun p : RoundCylinderSpace => p.2) (G.symm_apply_apply (z.1, z.2.val))
  right_inv z := by
    apply Prod.ext
    · change (G (G.symm (z.1, z.2.val))).1 = z.1
      exact congrArg (fun p : RoundCylinderSpace => p.1) (G.apply_symm_apply (z.1, z.2.val))
    · apply Subtype.ext
      change (G (G.symm (z.1, z.2.val))).2 = z.2.val
      exact congrArg (fun p : RoundCylinderSpace => p.2) (G.apply_symm_apply (z.1, z.2.val))
  continuous_toFun := by
    have h : Continuous (fun z : UnitTwoSphere × Set.Ioo (0 : ℝ) 1 =>
        G (z.1, z.2.val)) := G.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact h.fst.prodMk (h.snd.subtype_mk _)
  continuous_invFun := by
    have h : Continuous (fun z : UnitTwoSphere × Set.Ioo (0 : ℝ) 1 =>
        G.symm (z.1, z.2.val)) := G.symm.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact h.fst.prodMk (h.snd.subtype_mk _)

variable {A : GeneralizedSliceCarrier.{u}} {U : Set A.carrier}
  (C : OpenCylinderModel U)



noncomputable def reparametrizeCylinder : OpenCylinderModel U where
  homeomorph := (cylinderStripHomeomorph G hG).symm.trans C.homeomorph
  coordinate := C.coordinate ∘ G.symm
  coordinate_eq z := C.coordinate_eq ((cylinderStripHomeomorph G hG).symm z)
  coordinate_smooth := C.coordinate_smooth.comp G.symm.contMDiff.contMDiffOn
    (fun _ hp => cylinderReparametrization_symm_mem G hG hp)
  inverse := G ∘ C.inverse
  inverse_mem x hx := cylinderReparametrization_mem G hG (C.inverse_mem x hx)
  left_inverse := by
    intro p hp
    change G (C.inverse (C.coordinate (G.symm p))) = p
    rw [C.left_inverse (cylinderReparametrization_symm_mem G hG hp), G.apply_symm_apply]
  right_inverse := by
    intro x hx
    change C.coordinate (G.symm (G (C.inverse x))) = x
    rw [G.symm_apply_apply, C.right_inverse hx]
  inverse_smooth := G.contMDiff.comp_contMDiffOn C.inverse_smooth


@[simp] theorem reparametrizeCylinder_coordinate (p : RoundCylinderSpace) :
    (reparametrizeCylinder G hG C).coordinate p = C.coordinate (G.symm p) := rfl


@[simp] theorem reparametrizeCylinder_inverse (x : A.carrier) :
    (reparametrizeCylinder G hG C).inverse x = G (C.inverse x) := rfl

end PoincareConjecture.M38
