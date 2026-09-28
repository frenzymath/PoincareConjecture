import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]




theorem curveVelocity_moving_labels (q : ℝ → ℝ → M) {psi : ℝ → ℝ} {t w : ℝ}
    (hq : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 n)
      (fun z : ℝ × ℝ => q z.1 z.2) (psi t, t))
    (hpsi : HasDerivAt psi w t) :
    curveVelocity (n := n) (fun r => q (psi r) r) t =
      w • curveVelocity (n := n) (fun y => q y t) (psi t) +
        curveVelocity (n := n) (fun r => q (psi t) r) t := by
  have hmd := hpsi.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r) t :=
    mdifferentiableAt_id
  have hvalue : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) psi t 1 = w := by
    rw [mfderiv_eq_fderiv, hpsi.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ w
  have hpair : mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (fun r => (psi r, r)) t 1 = (w, 1) := by
    rw [mfderiv_prodMk hmd hid]
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) psi t 1,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r) t 1) = (w, 1)
    rw [hvalue]
    congr 1
    exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (mfderiv_id (I := 𝓘(ℝ, ℝ)))
  have hchain := mfderiv_comp_apply
    (f := fun r => (psi r, r)) (g := fun z : ℝ × ℝ => q z.1 z.2)
    t hq (hmd.prodMk hid) (1 : ℝ)
  rw [hpair] at hchain
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n)
    (v := (w, 1)) hq
  have hspatial : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) (psi t) w =
      w • curveVelocity (n := n) (fun y => q y t) (psi t) := by
    simpa only [curveVelocity, smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) (psi t)).map_smul w (1 : ℝ)
  exact hchain.trans (hsplit.trans (congrArg
    (fun V => V + curveVelocity (n := n) (fun r => q (psi t) r) t) hspatial))

variable [IsManifold (𝓡 n) ∞ M] {a b : ℝ}




theorem curvatureVector_eq_acceleration_sub_tangent
    (F : RicciFlow n M (Set.Icc a b)) (q : ℝ → ℝ → M) {t x v' : ℝ}
    (hX : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨q y t, curveVelocity (n := n) (fun z => q z t) y⟩ :
        TangentBundle (𝓡 n) M)) x)
    (hv : HasDerivAt (curveSpeed F q t) v' x)
    (hne : curveSpeed F q t x ≠ 0) :
    m62CurvatureVector F q t x =
      (curveSpeed F q t x ^ 2)⁻¹ •
          rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
            (fun y => curveVelocity (n := n) (fun z => q z t) y) x -
        (v' / curveSpeed F q t x ^ 3) •
          curveVelocity (n := n) (fun y => q y t) x := by
  unfold m62CurvatureVector m62SpatialDerivative spatialUnitTangent
  rw [M62.pullback_smul (F.connection t) (hv.fun_inv hne) hX]
  simp only [smul_add, smul_smul]
  have hcoeff : (curveSpeed F q t x)⁻¹ * (-v' / curveSpeed F q t x ^ 2) =
      -(v' / curveSpeed F q t x ^ 3) := by
    field_simp
  have hsquare : (curveSpeed F q t x)⁻¹ * (curveSpeed F q t x)⁻¹ =
      (curveSpeed F q t x ^ 2)⁻¹ := by
    rw [pow_two, mul_inv]
  rw [hcoeff, hsquare, neg_smul, sub_eq_add_neg, add_comm]





theorem normal_equation_of_parabolic_gauge
    (F : RicciFlow n M (Set.Icc a b)) (q : ℝ → ℝ → M) (psi : ℝ → ℝ → ℝ)
    {t x v' : ℝ}
    (hq : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 n)
      (fun z : ℝ × ℝ => q z.1 z.2) (psi x t, t))
    (hspace : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t))
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨q y t, spatialUnitTangent F q t y⟩ :
        TangentBundle (𝓡 n) M)) (psi x t))
    (hlabels : Differentiable ℝ (fun y => psi y t))
    (hpos : ∀ y, 0 < deriv (fun z => psi z t) y)
    (hX : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨q y t, curveVelocity (n := n) (fun z => q z t) y⟩ :
        TangentBundle (𝓡 n) M)) (psi x t))
    (hv : HasDerivAt (curveSpeed F q t) v' (psi x t))
    (hne : curveSpeed F q t (psi x t) ≠ 0)
    (hgauge : curveVelocity (n := n) (fun r => q (psi x t) r) t =
      (curveSpeed F q t (psi x t) ^ 2)⁻¹ •
        rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
          (fun y => curveVelocity (n := n) (fun z => q z t) y) (psi x t))
    (hode : HasDerivAt (psi x) (-(v' / curveSpeed F q t (psi x t) ^ 3)) t) :
    curveVelocity (n := n) (fun r => q (psi x r) r) t =
      m62CurvatureVector F (fun y r => q (psi y r) r) t x := by
  have hnormal : curveVelocity (n := n) (fun r => q (psi x r) r) t =
      m62CurvatureVector F q t (psi x t) := by
    rw [curveVelocity_moving_labels q hq hode, hgauge,
      curvatureVector_eq_acceleration_sub_tangent F q hX hv hne,
      neg_smul, sub_eq_add_neg, add_comm]
  have hcurvature := curvatureVector_comp F q hspace hlabels hpos hS
  exact hnormal.trans hcurvature.symm

end PoincareConjecture.M63
