import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTangentFrame
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Topology ContDiff

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))





theorem m64_exists_smooth_metric_normal_coordinates
    {c : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (h0 : 0 ∈ I)
    (hc : ContDiffOn ℝ ∞ c I)
    {U : Set E} (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ContDiffOn ℝ ∞ G U) (hcU : MapsTo c I U)
    (hpos : ∀ t ∈ I, 0 < G (c t) (deriv c t) (deriv c t)) :
    ∃ F : E → E, ∃ B : E ≃L[ℝ] E,
      ContDiffOn ℝ ∞ F {z : E | z 0 ∈ I} ∧
      HasFDerivAt F (B : E →L[ℝ] E) 0 ∧
      (∀ t : ℝ, F (EuclideanSpace.single 0 t) = c t) ∧
      (∀ t ∈ I, fderiv ℝ F (EuclideanSpace.single 0 t)
        (EuclideanSpace.single 0 1) = deriv c t) ∧
      ∀ t ∈ I, ∀ z : E, z 0 = 0 →
        G (c t) (deriv c t) (fderiv ℝ F (EuclideanSpace.single 0 t) z) = 0 := by
  obtain ⟨B, hB0, hB⟩ := m64_exists_metric_tangent_frame
    (G (c 0)) (deriv c 0) (hpos 0 h0)
  let X : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) 0
  let e : E := EuclideanSpace.single 0 1
  let J : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - X.smulRight e
  let v := deriv c
  let d : ℝ → ℝ := fun t => G (c t) (v t) (v t)
  let N : ℝ → E →L[ℝ] E := fun t => (B : E →L[ℝ] E) -
    ((G (c t) (v t)).comp (B : E →L[ℝ] E)).smulRight ((d t)⁻¹ • v t)
  let F : E → E := fun z => c (X z) + N (X z) (J z)
  have hX (z : E) : X z = z 0 := rfl
  have he : X e = 1 := by simp [X, e]
  have hJ (z : E) : J z = z - z 0 • e := rfl
  have hJ0 (z : E) : X (J z) = 0 := by
    rw [hJ, map_sub, map_smul, he, smul_eq_mul, mul_one, hX, sub_self]
  have hJe (t : ℝ) : J (EuclideanSpace.single 0 t) = 0 := by
    rw [hJ]
    ext i
    by_cases hi : i = 0 <;> simp [e, hi]
  have hv : ContDiffOn ℝ ∞ v I := hc.deriv_of_isOpen hI (by simp)
  have hGc : ContDiffOn ℝ ∞ (fun t => G (c t)) I := hG.comp hc hcU
  have hGv : ContDiffOn ℝ ∞ (fun t => G (c t) (v t)) I := hGc.clm_apply hv
  have hd : ContDiffOn ℝ ∞ d I := hGv.clm_apply hv
  have hd0 : ∀ t ∈ I, d t ≠ 0 := fun t ht => (hpos t ht).ne'
  have hN : ContDiffOn ℝ ∞ N I := by
    exact contDiffOn_const.sub
      ((hGv.clm_comp contDiffOn_const).smulRight ((hd.inv hd0).smul hv))
  have hF : ContDiffOn ℝ ∞ F {z : E | z 0 ∈ I} :=
    (hc.comp X.contDiff.contDiffOn (fun _ hz => hz)).add
      ((hN.comp X.contDiff.contDiffOn (fun _ hz => hz)).clm_apply J.contDiff.contDiffOn)
  have haxis (t : ℝ) : F (EuclideanSpace.single 0 t) = c t := by
    simp [F, hX, hJe]
  have hFD (t : ℝ) (ht : t ∈ I) : HasFDerivAt F
      (X.smulRight (v t) + (N t).comp J) (EuclideanSpace.single 0 t) := by
    have hcD := ((hc.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
    have hNdiff := (hN.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
    have hct : HasFDerivAt (fun z : E => c (X z)) (X.smulRight (v t))
        (EuclideanSpace.single 0 t) := by
      convert! hcD.hasFDerivAt.comp (EuclideanSpace.single 0 t) X.hasFDerivAt using 1
    have hNt := hNdiff.hasFDerivAt.comp (EuclideanSpace.single 0 t) X.hasFDerivAt
    have hx : X (EuclideanSpace.single 0 t) = t := by simp [X]
    have hh := hNt.clm_apply J.hasFDerivAt
    rw [hJe] at hh
    convert! hct.add hh using 1
    simp [hx]
  have hnormal (t : ℝ) (ht : t ∈ I) (z : E) : G (c t) (v t) (N t z) = 0 := by
    change G (c t) (v t) (B z - G (c t) (v t) (B z) • ((d t)⁻¹ • v t)) = 0
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change G (c t) (v t) (B z) - G (c t) (v t) (B z) * ((d t)⁻¹ * d t) = 0
    rw [inv_mul_cancel₀ (hd0 t ht), mul_one, sub_self]
  have hbase : X.smulRight (v 0) + (N 0).comp J = (B : E →L[ℝ] E) := by
    apply ContinuousLinearMap.ext
    intro z
    have hz : G (c 0) (v 0) (B (J z)) = 0 := by
      rw [hB]
      change _ * X (J z) = 0
      rw [hJ0, mul_zero]
    change X z • v 0 + (B (J z) - G (c 0) (v 0) (B (J z)) •
      ((d 0)⁻¹ • v 0)) = B z
    rw [hz, zero_smul, sub_zero, hJ, map_sub, map_smul, hB0]
    change z 0 • v 0 + (B z - z 0 • v 0) = B z
    abel
  refine ⟨F, B, hF, ?_, haxis, ?_, ?_⟩
  · have hz : (EuclideanSpace.single 0 0 : E) = 0 := by ext i; simp
    simpa only [hbase, hz] using hFD 0 h0
  · intro t ht
    rw [(hFD t ht).fderiv]
    change X e • v t + N t (J e) = v t
    rw [he, hJe 1, map_zero, one_smul, add_zero]
  · intro t ht z hz
    rw [(hFD t ht).fderiv]
    change G (c t) (v t) (X z • v t + N t (J z)) = 0
    rw [hX, hz, zero_smul, zero_add]
    exact hnormal t ht (J z)

end PoincareConjecture
