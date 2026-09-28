import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.AxialShift



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.CylinderGluing

local notation "Cyl" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem mfderiv_axial_map_apply {k : ℝ → ℝ} {a : ℝ}
    (z : RoundCylinderSpace) (hk : HasDerivAt k a z.2)
    (v : RoundCylinderTangent z) :
    mfderiv Cyl Cyl (fun p : RoundCylinderSpace => (p.1, k p.2)) z v =
      (v.1, a * v.2) := by
  have hkd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k z.2 :=
    hk.differentiableAt.mdifferentiableAt
  have hcomp : MDifferentiableAt Cyl 𝓘(ℝ, ℝ)
      (fun p : RoundCylinderSpace => k p.2) z := hkd.comp z mdifferentiableAt_snd
  erw [mfderiv_prodMk mdifferentiableAt_fst hcomp,
    mfderiv_fst, mfderiv_comp z hkd mdifferentiableAt_snd,
    mfderiv_snd, mfderiv_eq_fderiv]
  change (v.1, fderiv ℝ k z.2 v.2) = (v.1, a * v.2)
  rw [fderiv_eq_deriv_mul, hk.deriv]



theorem round_metric_le_axial_pullback {k : ℝ → ℝ} {a : ℝ}
    (z : RoundCylinderSpace) (hk : HasDerivAt k a z.2) (ha : 1 ≤ a)
    (v : RoundCylinderTangent z) :
    EvolvingRoundCylinderMetric 0 z v v ≤
      EvolvingRoundCylinderMetric 0 (z.1, k z.2)
        (mfderiv Cyl Cyl (fun p : RoundCylinderSpace => (p.1, k p.2)) z v)
        (mfderiv Cyl Cyl (fun p : RoundCylinderSpace => (p.1, k p.2)) z v) := by
  rw [mfderiv_axial_map_apply z hk]
  dsimp [EvolvingRoundCylinderMetric]
  have hh : v.2 ^ 2 ≤ (a * v.2) ^ 2 := by
    nlinarith [sq_nonneg v.2, mul_nonneg (show 0 ≤ a ^ 2 - 1 by nlinarith) (sq_nonneg v.2)]
  nlinarith



theorem inverse_axial_expansion_round_metric_le
    (J : Diffeomorph Cyl Cyl RoundCylinderSpace RoundCylinderSpace ∞)
    (a : ℝ) {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (hJ : ∀ p : RoundCylinderSpace,
      J p = (p.1, p.2 + d * Real.smoothTransition ((p.2 - a) / δ)))
    (z : RoundCylinderSpace) (v : RoundCylinderTangent z) :
    EvolvingRoundCylinderMetric 0 (J.symm z)
        (mfderiv Cyl Cyl J.symm z v) (mfderiv Cyl Cyl J.symm z v) ≤
      EvolvingRoundCylinderMetric 0 z v v := by
  let k : ℝ → ℝ := fun t => t + d * Real.smoothTransition ((t - a) / δ)
  have hkderiv (t : ℝ) : HasDerivAt k
      (1 + d * (deriv Real.smoothTransition ((t - a) / δ) / δ)) t := by
    have hs := (((Real.smoothTransition.contDiff :
      ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp))
      ((t - a) / δ)).hasDerivAt
    convert (hasDerivAt_id t).add ((hs.comp t
      (((hasDerivAt_id t).sub_const a).div_const δ)).const_mul d) using 1 <;>
      first | rfl | simp [div_eq_mul_inv]
  have hge (t : ℝ) : 1 ≤ 1 + d *
      (deriv Real.smoothTransition ((t - a) / δ) / δ) := by
    have hnonneg := Real.smoothTransition.monotone.deriv_nonneg (x := (t - a) / δ)
    exact le_add_of_nonneg_right (mul_nonneg hd (div_nonneg hnonneg hδ.le))
  have hJfun : (J : RoundCylinderSpace → RoundCylinderSpace) =
      fun p => (p.1, k p.2) := funext hJ
  have hbound := round_metric_le_axial_pullback (J.symm z)
    (hkderiv (J.symm z).2) (hge (J.symm z).2) (mfderiv Cyl Cyl J.symm z v)
  rw [← hJfun] at hbound
  have hcomp := mfderiv_comp z
    (J.contMDiff.mdifferentiable (by simp) (J.symm z))
    (J.symm.contMDiff.mdifferentiable (by simp) z)
  have hid : (J : RoundCylinderSpace → RoundCylinderSpace) ∘ J.symm = id :=
    funext J.apply_symm_apply
  rw [hid, mfderiv_id] at hcomp
  have hv : mfderiv Cyl Cyl J (J.symm z) (mfderiv Cyl Cyl J.symm z v) = v :=
    (congrArg (fun L => L v) hcomp).symm
  have hpoint : ((J.symm z).1, k (J.symm z).2) = z :=
    (hJ (J.symm z)).symm.trans (J.apply_symm_apply z)
  dsimp only [TangentSpace] at hv hbound
  rw [hv, hpoint] at hbound
  exact hbound

end PoincareConjecture.CylinderGluing
