import Mathlib.Geometry.Manifold.Instances.Sphere
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Filter Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩



theorem exists_boundary_marking_of_prescribed_ribbon_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w a : Real} (hw : 0 < w) (ha : 0 < a) (haw : a < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1) :
    ∃ r : Real, 1 < r ∧ a * r < w ∧ ∃ f : E1 → S1,
      InjOn f (closedBall 0 r) ∧
      (∀ x ∈ closedBall (0 : E1) r,
        IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x) ∧
      ∀ x ∈ closedBall (0 : E1) r,
        A (f x) = R (WithLp.toLp 2 ![a * x 0, 0]) := by
  classical
  have hratio : 1 < w / a := (lt_div_iff₀ ha).mpr (by simpa using haw)
  obtain ⟨r, hr, hrw⟩ := exists_between hratio
  have har : a * r < w := by
    have := (lt_div_iff₀ ha).mp hrw
    simpa only [mul_comm] using this
  let L : E1 → E2 := fun x => WithLp.toLp 2 ![a * x 0, 0]
  have hL : ContDiff Real ∞ L := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 1)).contDiff
    · exact contDiff_const
  let U : Opens E1 := ⟨(fun x : E1 => a * x 0) ⁻¹' Ioo (-w) w,
    isOpen_Ioo.preimage (continuous_const.mul
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 1)).continuous)⟩
  have hmem (x : E1) (hx : x ∈ U) : A.symm (R (L x)) ∈ sphere (0 : E2) 1 := by
    obtain ⟨y, hy, hye⟩ := hedge (a * x 0) hx
    rw [← hye, A.symm_apply_apply]
    exact hy
  have hzero : (0 : E1) ∈ U := by
    change a * (0 : E1) 0 ∈ Ioo (-w) w
    simp only [PiLp.zero_apply, mul_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos hw, hw⟩
  let p : S1 := ⟨A.symm (R (L 0)), hmem 0 hzero⟩
  let f : E1 → S1 := fun x => if hx : x ∈ U then ⟨A.symm (R (L x)), hmem x hx⟩ else p
  have hfval (x : E1) (hx : x ∈ U) : (f x : E2) = A.symm (R (L x)) := by
    simp only [f, dif_pos hx]
  have hfV : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun x : U => f (x : E1)) := by
    have h := (A.symm.contMDiff.comp (R.contMDiff.comp
      (hL.contMDiff.comp contMDiff_subtype_val))).codRestrict_sphere (n := 1)
        (fun x : U => hmem x x.property)
    convert! h using 1
    funext x
    exact Subtype.ext (hfval x x.property)
  have hfs : ContMDiffOn (𝓡 1) (𝓡 1) ∞ f U := by
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hfV ⟨x, hx⟩)).contMDiffWithinAt
  let C : E2 → E1 := fun y => WithLp.toLp 2 ![y 0 / a]
  have hC : ContDiff Real ∞ C := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.div_const a
  let T : S1 → E1 := fun q => C (R.symm (A q))
  have hT : ContMDiff (𝓡 1) (𝓡 1) ∞ T :=
    hC.contMDiff.comp (R.symm.contMDiff.comp (A.contMDiff.comp contMDiff_coe_sphere))
  have hleft (x : E1) (hx : x ∈ U) : T (f x) = x := by
    dsimp [T]
    rw [hfval x hx, A.apply_symm_apply, R.symm_apply_apply]
    ext i
    fin_cases i
    change a * x 0 / a = x 0
    field_simp
  have hbij (x : E1) (hx : x ∈ U) : Bijective (mfderiv (𝓡 1) (𝓡 1) f x) := by
    have hfx := hfs.contMDiffAt (U.isOpen.mem_nhds hx)
    have heq : T ∘ f =ᶠ[𝓝 x] id := by
      filter_upwards [U.isOpen.mem_nhds hx] with y hy
      exact hleft y hy
    have hchain := mfderiv_comp x ((hT (f x)).mdifferentiableAt (by simp))
      (hfx.mdifferentiableAt (by simp))
    have hsame := heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 1)
    rw [hchain, mfderiv_id] at hsame
    have hinj : Injective (mfderiv (𝓡 1) (𝓡 1) f x) := by
      intro u v huv
      have hh := congrArg (mfderiv (𝓡 1) (𝓡 1) T (f x)) huv
      have hu := congrArg (fun D => D u) hsame
      have hv := congrArg (fun D => D v) hsame
      exact hu.symm.trans (hh.trans hv)
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E1) (V₂ := E1) (f := (mfderiv (𝓡 1) (𝓡 1) f x).toLinearMap) rfl).mp hinj⟩
  have hsub : closedBall (0 : E1) r ⊆ U := by
    intro x hx
    have hnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hcoord' : |x 0| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    have hcoord : |x 0| ≤ r := hcoord'.trans hnorm
    have hbound : |a * x 0| < w := by
      rw [abs_mul, abs_of_pos ha]
      exact (mul_le_mul_of_nonneg_left hcoord ha.le).trans_lt har
    exact abs_lt.mp hbound
  refine ⟨r, hr, har, f, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [← hleft x (hsub hx), ← hleft y (hsub hy), hxy]
  · intro x hx
    exact Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv
      U.isOpen hfs hbij ⟨x, hsub hx⟩
  · intro x hx
    rw [hfval x (hsub hx), A.apply_symm_apply]

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
