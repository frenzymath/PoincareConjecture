import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Differential

/-!
# Finite scalar regularity under C2 relabeling

A positive C2 change of labels gives C1 speed and C2 squared or positive
regularized curvature. These are the actual scalars of the displayed curve;
no infinite regularity of the labels is asserted. Source: MT2007 Claim 19.11
and Corollary 19.13, p. 446; correction pp. 6-9; see
`2026-09-21-c2-slope-preservation.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) {c d : ℝ → ℝ → M}
  {phi : ℝ → ℝ} {t x : ℝ}

/-- Speed retains the derivative factor on each included relabeled slice.
MT2007 Lemma 19.6, pp. 441-442. -/
theorem speed_eq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    curveSpeed F c t x = deriv phi x * curveSpeed F d t (phi x) := by
  rw [curveSpeed_congr_slice F hcd]
  exact curveSpeed_comp F d
    ((hd.spatial_regular t ht (phi x)).mdifferentiableAt (by norm_num))
    (hphi x).hasDerivAt (hpos x).le

/-- Actual squared curvature is the composition with the fixed label map.
MT2007 Lemma 19.6, pp. 441-442; correction pp. 6-8. -/
theorem curvatureSquared_eq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    m62CurvatureSquared F c t x = m62CurvatureSquared F d t (phi x) := by
  rw [curvatureSquared_congr_slice F hcd]
  exact curvatureSquared_comp F d
    ((hd.spatial_regular t ht).mdifferentiable (by norm_num)) hphi hpos
    ((M62.unitTangent_contMDiff F d hd ht (phi x)).mdifferentiableAt (by simp))

/-- C2 labels and the original C1 speed give C1 actual speed, including
the endpoints of the relabeling slab. Correction Lemma 0.4, pp. 7-8. -/
theorem speed_contDiff_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 2 phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    ContDiff ℝ 1 (curveSpeed F c t) := by
  have heq : curveSpeed F c t = fun y => deriv phi y * curveSpeed F d t (phi y) :=
    funext fun _ => speed_eq_of_relabeling F hd
      (hphi.differentiable (by norm_num)) hpos ht hcd
  rw [heq]
  have hphi' : ContDiff ℝ 1 (deriv phi) := hphi.deriv'
  exact hphi'.mul ((M62.speed_contDiff F d hd ht).comp (hphi.of_le (by norm_num)))

/-- Smooth original squared curvature composed with C2 labels is C2 on
each interior spatial slice. Correction Corollary 0.3, pp. 6-7. -/
theorem curvatureSquared_contDiff_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 2 phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Ioo a b) (hcd : ∀ y, c y t = d (phi y) t) :
    ContDiff ℝ 2 (m62CurvatureSquared F c t) := by
  have heq : m62CurvatureSquared F c t = fun y => m62CurvatureSquared F d t (phi y) :=
    funext fun _ => curvatureSquared_eq_of_relabeling F hd
      (hphi.differentiable (by norm_num)) hpos (Ioo_subset_Icc_self ht) hcd
  rw [heq]
  have hq : ContDiff ℝ ∞ (m62CurvatureSquared F d t) :=
    (M62.curvatureSquared_contDiffOn F d hd).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  exact (hq.of_le (by decide)).comp hphi

/-- Positive regularization has C2 spatial regularity after a C2 relabeling,
including at curvature zeros. Correction Corollary 0.3, pp. 6-7. -/
theorem regularized_contDiff_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 2 phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Ioo a b) (hcd : ∀ y, c y t = d (phi y) t)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ContDiff ℝ 2 (m62RegularizedCurvature F c epsilon t) := by
  exact ((curvatureSquared_contDiff_of_relabeling F hd hphi hpos ht hcd).add
    contDiff_const).sqrt (fun y => (M62.regularized_radicand_pos F c hepsilon t y).ne')

end PoincareMT.M63
