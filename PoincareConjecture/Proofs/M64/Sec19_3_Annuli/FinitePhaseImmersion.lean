import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FinitePhaseCurrent






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64Annulus_affine_phase_within_immersion
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map m64AnnulusDomain)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {c : ℝ} (hc : c ≠ 0) (hphase : ∀ p ∈ m64AnnulusDomain,
      (A.map p).2 = P.circle.quotient (c * p 1)) :
    ∀ p ∈ m64AnnulusDomain,
      0 < m64AnnulusWithinGram (P.flow.metric t) A.map p 0 0 ∧
      0 < m64AnnulusWithinGram (P.flow.metric t) A.map p 1 1 ∧
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 (n + 1)) A.map m64AnnulusDomain p) := by
  have hradial := m64Annulus_affine_phase_radial_ne_zero P t hAc hAi hc hphase
  have hconf := m64AnnulusWithinGram_modulus_conformal A r hAc hAi hconformal
  intro p hp
  let d := mfderivWithin (𝓡 2) (𝓡 (n + 1)) A.map m64AnnulusDomain p
  let e0 : LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ 0
  let e1 : LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ 1
  let G := (P.flow.metric t).inner (A.map p)
  have h11 : 0 < G (d e1) (d e1) := (P.flow.metric t).pos _ _ (hradial p hp)
  have hdiag := (hconf p hp).1
  have h00 : 0 < G (d e0) (d e0) := by
    have hpos := mul_pos (inv_pos.mpr hr) h11
    change 0 < r⁻¹ * m64AnnulusWithinGram (P.flow.metric t) A.map p 1 1 at hpos
    rw [← hdiag] at hpos
    exact (mul_pos_iff_of_pos_left hr).mp hpos
  have h01 : G (d e0) (d e1) = 0 := (hconf p hp).2
  have h10 : G (d e1) (d e0) = 0 :=
    ((P.flow.metric t).symm _ _ _).trans h01
  refine ⟨h00, h11, ?_⟩
  have hdecomp (v : LoopPlane) : v = v 0 • e0 + v 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1]
  have hd (v : LoopPlane) : d v = v 0 • d e0 + v 1 • d e1 := by
    rw [← map_smul, ← map_smul, ← map_add, ← hdecomp]
  have hker (v : LoopPlane) (hv : d v = 0) : v = 0 := by
    have h0 := congrArg (fun w => G w (d e0)) hv
    have h1 := congrArg (fun w => G w (d e1)) hv
    rw [hd v] at h0 h1
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      h10, h01, mul_zero, zero_add, add_zero, map_zero, zero_apply] at h0 h1
    have hv0 : v 0 = 0 := (mul_eq_zero.mp h0).resolve_right h00.ne'
    have hv1 : v 1 = 0 := (mul_eq_zero.mp h1).resolve_right h11.ne'
    rw [hdecomp v, hv0, hv1, zero_smul, zero_smul, add_zero]
  intro v w hvw
  exact sub_eq_zero.mp (hker (v - w) (by rw [map_sub, hvw, sub_self]))

end PoincareConjecture
