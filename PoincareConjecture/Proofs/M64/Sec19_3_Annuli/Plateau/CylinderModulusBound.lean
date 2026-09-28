import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ProductCircleEnergy

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64CirclePhase_cylinder_modulus_bound (P : M62.CircleProductData F circumference)
    (t : ℝ) (f : LoopPlane → P.charts.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f)
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L)
    (hquot : ∀ p, P.circle.quotient (L p) = (f p).2)
    {d : ℝ} (hd : d ≠ 0) (hshift : ∀ x s,
      L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d)
    {r E : ℝ} (hr : 0 < r)
    (hE : (∫ p in interior m64AnnulusDomain,
      (r * m60AreaGram (P.flow.metric t) f p 0 0 +
        r⁻¹ * m60AreaGram (P.flow.metric t) f p 1 1) / 2) ≤ E) :
    r ≤ 2 * curvePeriod * E / d ^ 2 := by
  let D : LoopPlane → ℝ := fun p =>
    (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2
  let Q : LoopPlane → ℝ := fun p =>
    (r * m60AreaGram (P.flow.metric t) f p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) f p 1 1) / 2
  have hD : IntegrableOn D (interior m64AnnulusDomain) volume :=
    (((hL.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hG (i j : Fin 2) : Continuous (fun p => m60AreaGram (P.flow.metric t) f p i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (m60AreaGram_continuous _ hf))
  have hQ : IntegrableOn Q (interior m64AnnulusDomain) volume :=
    (((hG 0 0).const_mul r).add ((hG 1 1).const_mul r⁻¹) |>.div_const 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hpoint (p : LoopPlane) : r * D p ≤ 2 * Q p := by
    have hcol := m64CirclePhase_column_sq_le_gram P t f hf L hL hquot p 0
    simp only [EuclideanSpace.basisFun_apply] at hcol
    have hscale := mul_le_mul_of_nonneg_left hcol hr.le
    have hv := mul_nonneg (inv_nonneg.mpr hr.le)
      (m60AreaGram_diagonal_nonneg (P.flow.metric t) f p 1)
    dsimp only [D, Q]
    linarith
  have hi := integral_mono (hD.const_mul r) (hQ.const_mul 2) hpoint
  rw [integral_const_mul, integral_const_mul] at hi
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hscaled := mul_le_mul_of_nonneg_left hi hperiod
  have hphase := mul_le_mul_of_nonneg_left (m64Annulus_phase_energy hL hshift) hr.le
  have hEscale := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * curvePeriod)
  change r * d ^ 2 ≤ r * (curvePeriod * ∫ p in interior m64AnnulusDomain, D p) at hphase
  change 2 * curvePeriod * (∫ p in interior m64AnnulusDomain, Q p) ≤
    2 * curvePeriod * E at hEscale
  apply (le_div_iff₀ (sq_pos_of_ne_zero hd)).mpr
  nlinarith

end PoincareConjecture
