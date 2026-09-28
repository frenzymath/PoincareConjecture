import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTangentFrame
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace PoincareConjecture

theorem m64_exists_C2_curve_straightening {n : ℕ}
    {c : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hc : ContDiff ℝ 2 c) (hregular : deriv c 0 ≠ 0)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U) (hcU : c 0 ∈ U) :
    ∃ H : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
        (EuclideanSpace ℝ (Fin (n + 1))),
      0 ∈ H.source ∧ H.target ⊆ U ∧ H 0 = c 0 ∧
      ContDiffOn ℝ 2 H H.source ∧ ContDiffOn ℝ 2 H.symm H.target ∧
      ∀ t : ℝ, H (EuclideanSpace.single 0 t) = c t := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  obtain ⟨B, hB0, -⟩ := m64_exists_metric_tangent_frame (innerSL ℝ (E := E))
    (deriv c 0) (real_inner_self_pos.mpr hregular)
  let X : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let axis : E := EuclideanSpace.single 0 1
  let J : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - X.smulRight axis
  let F : E → E := fun z => c (X z) + B (J z)
  have hX (t : ℝ) : X (EuclideanSpace.single 0 t) = t := by
    change (EuclideanSpace.single 0 t : EuclideanSpace ℝ (Fin (n + 1))) 0 = t
    simp
  have hJaxis (t : ℝ) : J (EuclideanSpace.single 0 t) = 0 := by
    change EuclideanSpace.single 0 t - X (EuclideanSpace.single 0 t) • axis = 0
    rw [hX]
    ext i
    change (EuclideanSpace.single 0 t : EuclideanSpace ℝ (Fin (n + 1))) i -
      t * (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (n + 1))) i = 0
    by_cases hi : i = 0 <;> simp [hi]
  have haxis (t : ℝ) : F (EuclideanSpace.single 0 t) = c t := by
    simp only [F, hX, hJaxis, map_zero, add_zero]
  have hF : ContDiff ℝ 2 F :=
    (hc.comp X.contDiff).add (B.contDiff.comp J.contDiff)
  have hF0 : F 0 = c 0 := by simp [F]
  have hD : HasFDerivAt F (B : E →L[ℝ] E) 0 := by
    have hcD := ((hc.differentiable (by norm_num)) 0).hasDerivAt
    have hdc : HasFDerivAt (fun z : E => c (X z)) (X.smulRight (deriv c 0)) 0 := by
      convert! hcD.hasFDerivAt.comp (0 : E) X.hasFDerivAt using 1
    have hdF := hdc.add (B.toContinuousLinearMap.hasFDerivAt.comp (0 : E) J.hasFDerivAt)
    convert! hdF using 1
    apply ContinuousLinearMap.ext
    intro z
    change B z = X z • deriv c 0 + B (z - X z • axis)
    rw [map_sub, map_smul, hB0]
    abel
  let H0 := hF.contDiffAt.toOpenPartialHomeomorph F hD (by norm_num)
  have h0H : (0 : E) ∈ H0.source :=
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hD (by norm_num)
  have hi : ContDiffAt ℝ 2 H0.symm (F 0) :=
    hF.contDiffAt.to_localInverse hD (by norm_num)
  obtain ⟨V0, hV0, hVi⟩ := hi.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVV, hV, hFV⟩ := mem_nhds_iff.mp
    (inter_mem hV0 (hU.mem_nhds (hF0.symm ▸ hcU)))
  let H := (H0.symm.restrOpen V hV).symm
  have hFt : F 0 ∈ H.target := ⟨H0.map_source h0H, hFV⟩
  have hzero : H.symm (F 0) = 0 := H0.left_inv h0H
  refine ⟨H, ?_, fun y hy => (hVV hy.2).2, hF0, hF.contDiffOn,
    hVi.mono (fun y hy => (hVV hy.2).1), haxis⟩
  simpa only [hzero] using H.map_target hFt

end PoincareConjecture
