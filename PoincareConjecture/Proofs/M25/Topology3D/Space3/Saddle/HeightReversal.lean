import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection

set_option autoImplicit false

open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem heightPlaneCoordinates_neg_snd (u : UnitTwoSphere) (p : E2 × ℝ) :
    (heightPlaneCoordinates (-u) ((heightPlaneCoordinates u).symm p)).2 = -p.2 := by
  rw [heightPlaneCoordinates_snd, coe_neg_sphere, inner_neg_left,
    ← heightPlaneCoordinates_snd u, ContinuousLinearEquiv.apply_symm_apply]

noncomputable def heightReversalPlaneDiffeomorph (u : UnitTwoSphere) (l : ℝ) :
    Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := by
  let Lp := heightPlaneCoordinates u
  let Lm := heightPlaneCoordinates (-u)
  let J : E2 → E2 := fun x => (Lm (Lp.symm (x, l))).1
  let K : E2 → E2 := fun x => (Lp (Lm.symm (x, -l))).1
  have hJ : ContDiff ℝ ∞ J := contDiff_fst.comp
    (Lm.contDiff.comp (Lp.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)))
  have hK : ContDiff ℝ ∞ K := contDiff_fst.comp
    (Lp.contDiff.comp (Lm.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)))
  exact {
    toEquiv := {
      toFun := J
      invFun := K
      left_inv := by
        intro x
        have hp : (J x, -l) = Lm (Lp.symm (x, l)) :=
          Prod.ext rfl (heightPlaneCoordinates_neg_snd u (x, l)).symm
        change (Lp (Lm.symm (J x, -l))).1 = x
        rw [hp, Lm.symm_apply_apply, Lp.apply_symm_apply]
      right_inv := by
        intro x
        have hh : (Lp (Lm.symm (x, -l))).2 = l := by
          simpa only [neg_neg] using heightPlaneCoordinates_neg_snd (-u) (x, -l)
        have hp : (K x, l) = Lp (Lm.symm (x, -l)) := Prod.ext rfl hh.symm
        change (Lm (Lp.symm (K x, l))).1 = x
        rw [hp, Lp.symm_apply_apply, Lm.apply_symm_apply] }
    contMDiff_toFun := hJ.contMDiff
    contMDiff_invFun := hK.contMDiff }

theorem heightReversalPlaneDiffeomorph_apply (u : UnitTwoSphere) (l : ℝ) (x : E2) :
    heightReversalPlaneDiffeomorph u l x =
      (heightPlaneCoordinates (-u) ((heightPlaneCoordinates u).symm (x, l))).1 := rfl

theorem heightReversalPlaneDiffeomorph_symm_apply (u : UnitTwoSphere) (l : ℝ) (x : E2) :
    (heightReversalPlaneDiffeomorph u l).symm x =
      (heightPlaneCoordinates u ((heightPlaneCoordinates (-u)).symm (x, -l))).1 := rfl

end PoincareConjecture.M25.Topology3D
