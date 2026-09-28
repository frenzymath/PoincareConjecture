import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafCoordinates

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def affineLeafLinearEquiv (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (hQ : Function.RightInverse J Q) :
    (F × Q0.ker) ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse
    (J.coprod ((ContinuousLinearMap.id ℝ E - J.comp Q).comp Q0.ker.subtypeL))
    (Q.prod (Q0.projKerOfRightInverse J h0))
    (fun z => by
      apply Prod.ext
      · change Q (J z.1 + ((z.2 : E) - J (Q z.2))) = z.1
        rw [map_add, map_sub, hQ, hQ, sub_self, add_zero]
      · change Q0.projKerOfRightInverse J h0
          (J z.1 + ((z.2 : E) - J (Q z.2))) = z.2
        rw [map_add, map_sub, projKerOfRightInverse_comp_inv,
          projKerOfRightInverse_apply_idem, projKerOfRightInverse_comp_inv,
          sub_zero, zero_add])
    (fun y => by
      change J (Q y) + ((y - J (Q0 y)) - J (Q (y - J (Q0 y)))) = y
      rw [Q.map_sub, hQ, J.map_sub]
      abel)

end ContinuousLinearMap

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_affineLeafMap_zeroSection (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (x0 x : F) (hQ : DifferentiableAt ℝ Q x) :
    HasFDerivAt (a.affineLeafMap Q x0)
      (a.contLinear.coprod ((ContinuousLinearMap.id ℝ E - a.contLinear.comp (Q x)).comp
        (Q x0).ker.subtypeL)) (x, 0) := by
  let H := (Q x0).ker
  have hx : HasFDerivAt (fun z : F × H => a z.1)
      (a.contLinear.comp (ContinuousLinearMap.fst ℝ F H)) (x, 0) :=
    a.hasFDerivAt.comp (x, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hz : HasFDerivAt (fun z : F × H => (z.2 : E))
      (H.subtypeL.comp (ContinuousLinearMap.snd ℝ F H)) (x, 0) :=
    H.subtypeL.hasFDerivAt.comp (x, (0 : H))
      (ContinuousLinearMap.snd ℝ F H).hasFDerivAt
  have hq : HasFDerivAt (fun z : F × H => Q z.1)
      ((fderiv ℝ Q x).comp (ContinuousLinearMap.fst ℝ F H)) (x, 0) :=
    hQ.hasFDerivAt.comp (x, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hd := (hx.add hz).sub (a.contLinear.hasFDerivAt.comp (x, (0 : H)) (hq.clm_apply hz))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [ContinuousLinearMap.coprod_apply]
  abel

theorem isInvertible_fderiv_affineLeafMap_zeroSection (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (x0 x : F) (hQ : DifferentiableAt ℝ Q x)
    (h0 : Function.RightInverse a.contLinear (Q x0))
    (hx : Function.RightInverse a.contLinear (Q x)) :
    (fderiv ℝ (a.affineLeafMap Q x0) (x, 0)).IsInvertible := by
  rw [(a.hasFDerivAt_affineLeafMap_zeroSection x0 x hQ).fderiv]
  exact ⟨a.contLinear.affineLeafLinearEquiv (Q x0) (Q x) h0 hx, rfl⟩

end ContinuousAffineMap
