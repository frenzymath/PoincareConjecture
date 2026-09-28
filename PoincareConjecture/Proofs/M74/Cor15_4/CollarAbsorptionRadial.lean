import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorption
import PoincareConjecture.Proofs.M74.Mathlib.SphereNormalize

set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M74

open M25.Topology3D

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem norm_smul_sphereNormalize (q0 : UnitTwoSphere) (x : StandardCapSpace) :
    ‖x‖ • (sphereNormalize q0 x).1 = x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [sphereNormalize, dif_neg hx]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

private noncomputable def radialLift (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞)
    (x : StandardCapSpace) : StandardCapSpace :=
  ‖x‖ • (K (sphereNormalize q0 x, ‖x‖)).1.1

private theorem radialLift_zero (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞) :
    radialLift q0 K 0 = 0 := by simp [radialLift]

private theorem radialLift_norm (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞)
    (x : StandardCapSpace) : ‖radialLift q0 K x‖ = ‖x‖ := by
  rw [radialLift, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
    mem_sphere_zero_iff_norm.mp (K (sphereNormalize q0 x, ‖x‖)).1.2, mul_one]

private theorem radialLift_normalize (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    sphereNormalize q0 (radialLift q0 K x) = (K (sphereNormalize q0 x, ‖x‖)).1 :=
  sphereNormalize_pos_smul q0 _ (norm_pos_iff.mpr hx)

private theorem radialLift_symm_left (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞)
    (hK : ∀ p, (K p).2 = p.2) (x : StandardCapSpace) :
    radialLift q0 K.symm (radialLift q0 K x) = x := by
  by_cases hx : x = 0
  · simp only [hx, radialLift_zero]
  · change ‖radialLift q0 K x‖ •
      (K.symm (sphereNormalize q0 (radialLift q0 K x), ‖radialLift q0 K x‖)).1.1 = x
    rw [radialLift_norm, radialLift_normalize q0 K hx]
    have hin : ((K (sphereNormalize q0 x, ‖x‖)).1, ‖x‖) =
        K (sphereNormalize q0 x, ‖x‖) :=
      Prod.ext rfl (hK (sphereNormalize q0 x, ‖x‖)).symm
    rw [hin, K.symm_apply_apply]
    exact norm_smul_sphereNormalize q0 x

private noncomputable def radialEquiv (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞)
    (hK : ∀ p, (K p).2 = p.2) : StandardCapSpace ≃ StandardCapSpace where
  toFun := radialLift q0 K
  invFun := radialLift q0 K.symm
  left_inv := radialLift_symm_left q0 K hK
  right_inv := by
    have hsymm (p : RoundCylinderSpace) : (K.symm p).2 = p.2 := by
      have h := congrArg Prod.snd (K.apply_symm_apply p)
      simpa only [hK] using h
    exact radialLift_symm_left q0 K.symm hsymm

private theorem radialLift_contMDiffAt (q0 : UnitTwoSphere)
    (K : Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (radialLift q0 K) x := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hn : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : StandardCapSpace => ‖y‖) x :=
    (contDiffAt_norm ℝ hx).contMDiffAt
  have hi : ContMDiffAt (𝓡 3) ICollar ∞
      (fun y => (sphereNormalize q0 y, ‖y‖)) x :=
    (sphereNormalize_contMDiffAt q0 hx).prodMk hn
  have hk : ContMDiffAt (𝓡 3) ICollar ∞
      (fun y => K (sphereNormalize q0 y, ‖y‖)) x :=
    K.contMDiff.contMDiffAt.comp x hi
  have hq : ContMDiffAt (𝓡 3) (𝓡 2) ∞
      (fun y => (K (sphereNormalize q0 y, ‖y‖)).1) x :=
    contMDiff_fst.contMDiffAt.comp x hk
  have hv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y => (K (sphereNormalize q0 y, ‖y‖)).1.1) x :=
    contMDiff_coe_sphere.contMDiffAt.comp x hq
  exact hn.smul hv

private theorem radialLift_collar_eq_isometry {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ} (hab : a < b)
    {x : StandardCapSpace} (hx : ‖x‖ ≤ a) :
    radialLift q0 (collarDiffeomorph D a b) x = D.isometry x := by
  rw [radialLift, collarDiffeomorph_eq_isometry D hab _ hx]
  change ‖x‖ • D.isometry (sphereNormalize q0 x).1 = D.isometry x
  rw [← D.isometry.map_smul, norm_smul_sphereNormalize]

noncomputable def radialDiffeomorph {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ := by
  let K := collarDiffeomorph D a b
  have hK (p : RoundCylinderSpace) : (K p).2 = p.2 := rfl
  let e := radialEquiv q0 K hK
  have hinv {x : StandardCapSpace} (hx : ‖x‖ ≤ a) : e.symm x = D.isometry.symm x := by
    have hn : ‖e.symm x‖ = ‖x‖ := radialLift_norm q0 K.symm x
    have hsmall : ‖e.symm x‖ ≤ a := by rw [hn]; exact hx
    have hforward : D.isometry (e.symm x) = x :=
      (radialLift_collar_eq_isometry D q0 hab hsmall).symm.trans (e.apply_symm_apply x)
    have h := congrArg D.isometry.symm hforward
    simpa only [D.isometry.symm_apply_apply] using h
  refine {
    toEquiv := e
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro x
    by_cases hx : x = 0
    · subst x
      apply D.isometry.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : StandardCapSpace) ha] with y hy
      exact radialLift_collar_eq_isometry D q0 hab (mem_ball_zero_iff.mp hy).le
    · exact radialLift_contMDiffAt q0 K hx
  · intro x
    by_cases hx : x = 0
    · subst x
      have hlin : ContDiff ℝ ∞ D.isometry.symm :=
        D.isometry.symm.toContinuousLinearEquiv.contDiff
      apply hlin.contMDiff.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : StandardCapSpace) ha] with y hy
      exact hinv (mem_ball_zero_iff.mp hy).le
    · exact radialLift_contMDiffAt q0 K.symm hx

@[simp] theorem radialDiffeomorph_apply {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (x : StandardCapSpace) :
    radialDiffeomorph D q0 ha hab x =
      ‖x‖ • (D.isotopy (collarCutoff a b ‖x‖) (sphereNormalize q0 x)).1 := rfl

@[simp] theorem radialDiffeomorph_zero {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    radialDiffeomorph D q0 ha hab 0 = 0 := radialLift_zero q0 _

@[simp] theorem radialDiffeomorph_norm {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (x : StandardCapSpace) :
    ‖radialDiffeomorph D q0 ha hab x‖ = ‖x‖ := radialLift_norm q0 _ x

@[simp] theorem radialDiffeomorph_symm_norm {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (x : StandardCapSpace) :
    ‖(radialDiffeomorph D q0 ha hab).symm x‖ = ‖x‖ := radialLift_norm q0 _ x

theorem radialDiffeomorph_eq_isometry {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {x : StandardCapSpace} (hx : ‖x‖ ≤ a) :
    radialDiffeomorph D q0 ha hab x = D.isometry x :=
  radialLift_collar_eq_isometry D q0 hab hx

theorem radialDiffeomorph_eq_map {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 : UnitTwoSphere) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {x : StandardCapSpace} (hx : b ≤ ‖x‖) :
    radialDiffeomorph D q0 ha hab x = ‖x‖ • (f (sphereNormalize q0 x)).1 := by
  rw [radialDiffeomorph_apply, collarCutoff_eq_one hab hx, D.isotopy_one]

theorem radialDiffeomorph_pos_smul {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (q0 q : UnitTwoSphere) {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : b ≤ r) :
    radialDiffeomorph D q0 ha hab (r • q.1) = r • (f q).1 := by
  have hrpos : 0 < r := ha.trans_le (hab.le.trans hr)
  have hn : ‖r • q.1‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos,
      mem_sphere_zero_iff_norm.mp q.2, mul_one]
  rw [radialDiffeomorph_eq_map D q0 ha hab (by rw [hn]; exact hr), hn,
    sphereNormalize_pos_smul q0 q hrpos]

end PoincareConjecture.M74
