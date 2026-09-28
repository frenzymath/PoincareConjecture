import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Filling



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

def upperPoint : S1 := ⟨EuclideanSpace.single 1 1, by simp⟩

private theorem contDiffOn_graph_shift (c : Real) :
    ContDiffOn Real ∞ (fun x : E2 =>
      WithLp.toLp 2 ![x 0, x 1 + c * Real.sqrt (1-(x 0)^2)] : E2 → E2)
      {x | |x 0| < 1} := by
  have hcoord (i : Fin 2) : ContDiffOn Real ∞ (fun x : E2 => x i) {x | |x 0| < 1} :=
    (EuclideanSpace.proj (𝕜 := Real) i).contDiff.contDiffOn
  have hs : ContDiffOn Real ∞ (fun x : E2 => Real.sqrt (1-(x 0)^2)) {x | |x 0| < 1} :=
    (contDiffOn_const.sub ((hcoord 0).pow 2)).sqrt (by
      intro x hx
      change |x 0| < 1 at hx
      have ha := abs_lt.mp hx
      nlinarith)
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact hcoord 0
  · exact (hcoord 1).add (contDiffOn_const.mul hs)



def upperBoundaryFlattening : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![x 0, x 1 - Real.sqrt (1-(x 0)^2)]
  invFun x := WithLp.toLp 2 ![x 0, x 1 + Real.sqrt (1-(x 0)^2)]
  source := {x | |x 0| < 1}
  target := {x | |x 0| < 1}
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' x _ := by ext i; fin_cases i <;> simp
  right_inv' x _ := by ext i; fin_cases i <;> simp
  open_source := isOpen_lt ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).continuous.abs)
    continuous_const
  open_target := isOpen_lt ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).continuous.abs)
    continuous_const
  contMDiffOn_toFun := by
    simpa only [neg_one_mul, sub_eq_add_neg] using (contDiffOn_graph_shift (-1)).contMDiffOn
  contMDiffOn_invFun := by
    simpa only [one_mul] using (contDiffOn_graph_shift 1).contMDiffOn

theorem upperPoint_mem_flattening : (upperPoint : E2) ∈ upperBoundaryFlattening.source := by
  norm_num [upperPoint, upperBoundaryFlattening]

theorem upperBoundaryFlattening_radial (t : Real) :
    upperBoundaryFlattening ((1+t) • (upperPoint : E2)) = WithLp.toLp 2 ![0, t] := by
  ext i
  fin_cases i <;> simp [upperBoundaryFlattening, upperPoint]

theorem upperBoundaryFlattening_circle_germ :
    ∀ᶠ x in 𝓝 (upperPoint : E2), x ∈ sphere (0 : E2) 1 →
      upperBoundaryFlattening x = WithLp.toLp 2 ![x 0, 0] := by
  have hpos : ∀ᶠ x : E2 in 𝓝 (upperPoint : E2), 0 < x 1 :=
    ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).continuous.continuousAt).eventually
      (Ioi_mem_nhds (by norm_num [upperPoint] : 0 < (upperPoint : E2) 1))
  filter_upwards [hpos] with x hx hs
  have hn : (x 0)^2 + (x 1)^2 = 1 := by
    have hn := EuclideanSpace.norm_sq_eq x
    rw [mem_sphere_zero_iff_norm.mp hs] at hn
    simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using hn.symm
  have hroot : Real.sqrt (1-(x 0)^2) = x 1 := by
    rw [show 1-(x 0)^2 = (x 1)^2 by linarith, Real.sqrt_sq hx.le]
  ext i
  fin_cases i <;> simp [upperBoundaryFlattening, hroot]



theorem exists_filling_adapted_to_ribbon_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hedge : ∀ s ∈ Ioo (-w) w, R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (hinside : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ A '' ball (0 : E2) 1) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      F '' closedBall (0 : E2) 1 = A '' closedBall (0 : E2) 1 ∧
      F '' ball (0 : E2) 1 = A '' ball (0 : E2) 1 ∧
      F '' sphere (0 : E2) 1 = A '' sphere (0 : E2) 1 ∧
      (F : E2 → E2) =ᶠ[𝓝 (upperPoint : E2)] (fun x => R (upperBoundaryFlattening x)) := by
  let P := upperBoundaryFlattening.trans R.toPartialDiffeomorph
  have hcoord : ∀ᶠ x : E2 in 𝓝 (upperPoint : E2), x 0 ∈ Ioo (-w) w :=
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).continuous.continuousAt).eventually
      (Ioo_mem_nhds (by simpa [upperPoint] using neg_neg_of_pos hw)
        (by simpa [upperPoint] using hw))
  apply exists_filling_with_boundary_germ A P upperPoint
    ⟨upperPoint_mem_flattening, mem_univ _⟩
  · filter_upwards [upperBoundaryFlattening_circle_germ, hcoord] with x hx hwx
    intro hs
    change R (upperBoundaryFlattening x) ∈ A '' sphere (0 : E2) 1
    rw [hx hs]
    exact hedge _ hwx
  · filter_upwards [hinside] with t ht
    change R (upperBoundaryFlattening ((1+t) • (upperPoint : E2))) ∈ _
    rw [upperBoundaryFlattening_radial]
    exact ht

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
