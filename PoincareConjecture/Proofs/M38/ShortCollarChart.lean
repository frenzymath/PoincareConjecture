import PoincareConjecture.Proofs.M38.ShortCollar









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}
  (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace A.carrier ∞)
  {ε a : ℝ} (ha : 0 < a) (haε : a ≤ ε)
  (hc : c.source = Set.univ ×ˢ Set.Ioo (-ε) ε)


noncomputable def shortCollarChart :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace A.carrier ∞ where
  toFun := shortCollar c a
  invFun := shortCollarInverse c a
  source := Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1
  target := shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  map_source' := fun z hz => ⟨z, hz, rfl⟩
  map_target' := by
    rintro x ⟨z, hz, rfl⟩
    rw [shortCollar_left_inverse c ha haε hc hz]
    exact hz
  left_inv' := fun _ hz => shortCollar_left_inverse c ha haε hc hz
  right_inv' := fun _ hx => shortCollar_right_inverse c ha haε hc hx
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := shortCollar_open c ha haε hc
  contMDiffOn_toFun := shortCollar_smooth c ha haε hc
  contMDiffOn_invFun := shortCollarInverse_smooth c ha haε hc


@[simp] theorem shortCollarChart_source :
    (shortCollarChart c ha haε hc).source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := rfl


@[simp] theorem shortCollarChart_target :
    (shortCollarChart c ha haε hc).target =
      shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := rfl


theorem shortCollarChart_target_original :
    (shortCollarChart c ha haε hc).target = c '' (Set.univ ×ˢ Set.Ioo (-a) a) :=
  shortCollar_image c ha


@[simp] theorem shortCollarChart_apply (z : RoundCylinderSpace) :
    shortCollarChart c ha haε hc z = c (z.1, a * z.2) := rfl


@[simp] theorem shortCollarChart_inverse (x : A.carrier) :
    (shortCollarChart c ha haε hc).symm x =
      ((c.symm x).1, (c.symm x).2 / a) := rfl


theorem shortCollarChart_central :
    shortCollarChart c ha haε hc '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      c '' (Set.univ ×ˢ ({0} : Set ℝ)) := shortCollar_central c (a := a)

end PoincareConjecture.M38
