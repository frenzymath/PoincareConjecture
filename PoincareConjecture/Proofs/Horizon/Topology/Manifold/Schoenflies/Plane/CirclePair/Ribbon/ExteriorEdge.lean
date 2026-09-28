import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.Ribbon.BoundaryChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Crossing



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)


def ribbonTransverseReflection : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![x 0, -x 1]
  invFun x := WithLp.toLp 2 ![x 0, -x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.neg
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.neg

@[simp] theorem ribbonTransverseReflection_apply (s t : Real) :
    ribbonTransverseReflection (WithLp.toLp 2 ![s, t]) = WithLp.toLp 2 ![s, -t] := rfl



theorem ribbon_inward_germ_of_exterior_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (houtside : ∀ᶠ t in 𝓝[>] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∉ A '' closedBall (0 : E2) 1) :
    ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ A '' ball (0 : E2) 1 := by
  let P := (upperBoundaryFlattening.trans R.toPartialDiffeomorph).trans
    A.symm.toPartialDiffeomorph
  have hp : (upperPoint : E2) ∈ P.source :=
    ⟨⟨upperPoint_mem_flattening, mem_univ _⟩, mem_univ _⟩
  have hcoord : ∀ᶠ x : E2 in 𝓝 (upperPoint : E2), x 0 ∈ Ioo (-w) w :=
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).continuous.continuousAt).eventually
      (Ioo_mem_nhds (by simpa [upperPoint] using neg_neg_of_pos hw)
        (by simpa [upperPoint] using hw))
  have hboundary : ∀ᶠ x in 𝓝 (upperPoint : E2),
      x ∈ sphere (0 : E2) 1 → P x ∈ sphere (0 : E2) 1 := by
    filter_upwards [upperBoundaryFlattening_circle_germ, hcoord] with x hx hwx hs
    change A.symm (R (upperBoundaryFlattening x)) ∈ sphere (0 : E2) 1
    rw [hx hs]
    obtain ⟨y, hy, heq⟩ := hedge _ hwx
    rw [← heq, A.symm_apply_apply]
    exact hy
  have hout : ∀ᶠ t in 𝓝[>] (0 : Real),
      1 < ‖P ((1 + t) • (upperPoint : E2))‖ := by
    filter_upwards [houtside] with t ht
    change 1 < ‖A.symm (R (upperBoundaryFlattening ((1 + t) • (upperPoint : E2))))‖
    rw [upperBoundaryFlattening_radial]
    apply lt_of_not_ge
    intro hnorm
    apply ht
    exact ⟨A.symm (R (WithLp.toLp 2 ![0, t])),
      mem_closedBall_zero_iff.mpr hnorm, A.apply_symm_apply _⟩
  have hin := inward_radial_germ_of_outward_boundary_germ P upperPoint hp hboundary hout
  filter_upwards [hin] with t ht
  change ‖A.symm (R (upperBoundaryFlattening ((1 + t) • (upperPoint : E2))))‖ < 1 at ht
  rw [upperBoundaryFlattening_radial] at ht
  exact ⟨A.symm (R (WithLp.toLp 2 ![0, t])),
    mem_ball_zero_iff.mpr ht, A.apply_symm_apply _⟩



theorem exists_filling_adapted_to_exterior_ribbon_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (houtside : ∀ᶠ t in 𝓝[>] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∉ A '' closedBall (0 : E2) 1) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      F '' closedBall (0 : E2) 1 = A '' closedBall (0 : E2) 1 ∧
      F '' ball (0 : E2) 1 = A '' ball (0 : E2) 1 ∧
      F '' sphere (0 : E2) 1 = A '' sphere (0 : E2) 1 ∧
      (F : E2 → E2) =ᶠ[𝓝 (upperPoint : E2)]
        (fun x => R (upperBoundaryFlattening x)) :=
  exists_filling_adapted_to_ribbon_edge A R hw hedge
    (ribbon_inward_germ_of_exterior_edge A R hw hedge houtside)


theorem ribbon_positive_inward_germ_of_negative_exterior_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (houtside : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∉ A '' closedBall (0 : E2) 1) :
    ∀ᶠ t in 𝓝[>] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ A '' ball (0 : E2) 1 := by
  have hneg : Tendsto (fun t : Real => -t) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using (tendsto_neg_nhdsGT_neg (a := (0 : Real)))
  have hin := ribbon_inward_germ_of_exterior_edge A
    (ribbonTransverseReflection.trans R) hw
    (by simpa using hedge) (by simpa using hneg.eventually houtside)
  simpa using hneg.eventually hin



theorem exists_filling_adapted_to_negative_exterior_ribbon_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (houtside : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∉ A '' closedBall (0 : E2) 1) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      F '' closedBall (0 : E2) 1 = A '' closedBall (0 : E2) 1 ∧
      F '' ball (0 : E2) 1 = A '' ball (0 : E2) 1 ∧
      F '' sphere (0 : E2) 1 = A '' sphere (0 : E2) 1 ∧
      (F : E2 → E2) =ᶠ[𝓝 (upperPoint : E2)]
        (fun x => R (ribbonTransverseReflection (upperBoundaryFlattening x))) := by
  have hneg : Tendsto (fun t : Real => -t) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using (tendsto_neg_nhdsGT_neg (a := (0 : Real)))
  exact exists_filling_adapted_to_exterior_ribbon_edge A
    (ribbonTransverseReflection.trans R) hw
    (by simpa using hedge) (by simpa using hneg.eventually houtside)

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
