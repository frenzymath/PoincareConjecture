import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarping

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (D : LeviCivitaData g)
  (hsec : D.NonnegativeSectionalCurvature)

include D hsec

theorem intrinsicWarpingRadius_monotoneOn :
    MonotoneOn (intrinsicWarpingRadius g hrotation hcomplete) (Ioi 0) := by
  intro a ha b hb hab
  exact axisWarpingRadius_monotoneOn D hrotation hsec hcomplete
    (radialArclengthOrderIso_symm_pos g hrotation hcomplete ha)
    (radialArclengthOrderIso_symm_pos g hrotation hcomplete hb)
    ((radialArclengthOrderIso g hrotation hcomplete).symm.monotone hab)

theorem intrinsicWarpingRadius_ratio_antitoneOn :
    AntitoneOn (fun s => intrinsicWarpingRadius g hrotation hcomplete s / s) (Ioi 0) := by
  let f := intrinsicWarpingRadius g hrotation hcomplete
  have hmean (s : ℝ) (hs : 0 < s) : deriv f s * s ≤ f s := by
    let R := radialArclengthOrderIso g hrotation hcomplete
    have h := axisWarpingSlope_mul_arclength_le D hrotation hsec
      (radialArclengthOrderIso_symm_pos g hrotation hcomplete hs)
    rw [(intrinsicWarpingRadius_hasDerivAt g hrotation hcomplete hs).deriv]
    change axisWarpingSlope g (R.symm s) * s ≤ axisWarpingRadius g (R.symm s)
    change axisWarpingSlope g (R.symm s) * R (R.symm s) ≤ _ at h
    simpa only [OrderIso.apply_symm_apply] using h
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt (fun r => f r / r)
      ((deriv f s * s - f s) / s ^ 2) s := by
    convert! (((intrinsicWarpingRadius_contDiff g hrotation hcomplete).differentiable
      (by simp) s).hasDerivAt.div (hasDerivAt_id s) hs.ne') using 1
    simp only [f, id_eq, mul_one]
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
  intro s hs
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmean s (interior_subset hs)))
    (sq_nonneg s)

theorem intrinsicWarpingRadius_anchored_variation {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    |intrinsicWarpingRadius g hrotation hcomplete b -
        intrinsicWarpingRadius g hrotation hcomplete a| ≤
      intrinsicWarpingRadius g hrotation hcomplete a / a * |b - a| := by
  let f := intrinsicWarpingRadius g hrotation hcomplete
  rcases le_total a b with hab | hba
  · have hmono := intrinsicWarpingRadius_monotoneOn g hrotation hcomplete D hsec ha hb hab
    have hratio := intrinsicWarpingRadius_ratio_antitoneOn g hrotation hcomplete D hsec
      ha hb hab
    have hcross := (div_le_div_iff₀ hb ha).mp hratio
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hab)]
    change f b - f a ≤ f a / a * (b - a)
    calc
      _ ≤ f a * (b - a) / a := (le_div_iff₀ ha).mpr (by nlinarith only [hcross])
      _ = _ := by ring
  · have hmono := intrinsicWarpingRadius_monotoneOn g hrotation hcomplete D hsec hb ha hba
    have hratio := intrinsicWarpingRadius_ratio_antitoneOn g hrotation hcomplete D hsec
      hb ha hba
    have hcross := (div_le_div_iff₀ ha hb).mp hratio
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hba)]
    change -(f b - f a) ≤ f a / a * -(b - a)
    calc
      _ ≤ f a * -(b - a) / a := (le_div_iff₀ ha).mpr (by nlinarith only [hcross])
      _ = _ := by ring

end PoincareConjecture.M35.Uniqueness
