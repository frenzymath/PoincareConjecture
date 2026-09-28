import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Fields
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.TangentialTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceSlab








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}



theorem scalarCurvature_posPart_le_levelScalar [T2Space M]
    (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (hx : 0 < D.levelQ f x) (K : ℝ) (hK : 0 ≤ K)
    (hsec : ∀ v w : TangentSpace (𝓡 (n + 1)) x,
      -K ≤ D.sectionalCurvature x v w) :
    let L := D.scalarCurvature x -
      2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) +
      D.levelGaussTerm f x
    max 0 (D.scalarCurvature x) ≤ 2 * max 0 L +
      2 * ((n + 1 : ℕ) : ℝ) ^ 2 * K - 2 * D.levelBochnerDifference f x := by
  have hRic := D.two_mul_ricci_unit_le_scalarCurvature_add x K hK hsec
    (D.levelUnitNormal f x) (D.inner_levelUnitNormal_self f x hx)
  have hR := D.scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound x K hsec
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg hn hK
  dsimp only
  simp only [Nat.cast_add, Nat.cast_one] at hR ⊢
  have hL := le_max_right 0 (D.scalarCurvature x -
    2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) +
    D.levelGaussTerm f x)
  unfold levelBochnerDifference
  apply max_le <;> nlinarith

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]




theorem integral_scalarCurvature_posPart_slab_le (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hc : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x ∈ f ⁻¹' Icc a b,
      mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {K : M → ℝ} (hKc : ContinuousOn K (f ⁻¹' Icc a b))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (hsec : ∀ x ∈ f ⁻¹' Icc a b, ∀ v w : TangentSpace (𝓡 (n + 1)) x,
      -K x ≤ D.sectionalCurvature x v w) :
    let U := g.regularDomain hf
    let L := fun x => D.scalarCurvature x -
      2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) +
      D.levelGaussTerm f x
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * (∫ x in f ⁻¹' Icc a b, max 0 (L x) ∂g.volumeMeasure) +
      2 * ((n + 1 : ℕ) : ℝ) ^ 2 * (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
      2 * (∫ z, D.levelMeanCurvature f (openLevelIncl f U a z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) a) -
      2 * (∫ z, D.levelMeanCurvature f (openLevelIncl f U b z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) b) := by
  let L := fun x => D.scalarCurvature x -
    2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) +
    D.levelGaussTerm f x
  have hq : f ⁻¹' Icc a b ⊆ {x | 0 < D.levelQ f x} := by
    intro x hx
    have hr := (g.mem_regularDomain_iff hf x).mpr (hreg x hx)
    change 0 < Real.sqrt (D.levelQ f x) at hr
    exact Real.sqrt_pos.mp hr
  have hLc : ContinuousOn L (f ⁻¹' Icc a b) :=
    (D.continuous_scalarCurvature.continuousOn.sub
      ((D.continuousOn_ricci_levelUnitNormal hf).mono hq |>.const_mul 2)).add
      ((D.continuousOn_levelGaussTerm hf).mono hq)
  have hLi : IntegrableOn (fun x => max 0 (L x)) (f ⁻¹' Icc a b) g.volumeMeasure :=
    (show ContinuousOn (fun x => max 0 (L x)) (f ⁻¹' Icc a b) from
      fun x hx => continuousWithinAt_const.max (hLc x hx)).integrableOn_compact hc
  have hRi : IntegrableOn (fun x => max 0 (D.scalarCurvature x))
      (f ⁻¹' Icc a b) g.volumeMeasure :=
    (continuous_const.max D.continuous_scalarCurvature).continuousOn.integrableOn_compact hc
  have hBi : IntegrableOn (D.levelBochnerDifference f) (f ⁻¹' Icc a b) g.volumeMeasure :=
    ((D.continuousOn_levelBochnerDifference hf).mono hq).integrableOn_compact hc
  have hKi := hKc.integrableOn_compact (μ := g.volumeMeasure) hc
  have hle := setIntegral_mono_on hRi
    (((hLi.const_mul 2).add (hKi.const_mul (2 * ((n + 1 : ℕ) : ℝ) ^ 2))).sub
      (hBi.const_mul 2)) (isClosed_Icc.preimage hf.continuous).measurableSet
    (fun x hx => D.scalarCurvature_posPart_le_levelScalar f x (hq hx) (K x)
      (hK x hx) (hsec x hx))
  change (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
    ∫ x in f ⁻¹' Icc a b, (2 * max 0 (L x) +
      2 * ((n + 1 : ℕ) : ℝ) ^ 2 * K x) - 2 * D.levelBochnerDifference f x
      ∂g.volumeMeasure at hle
  rw [integral_sub (f := fun x => 2 * max 0 (L x) +
      2 * ((n + 1 : ℕ) : ℝ) ^ 2 * K x) ((hLi.const_mul 2).add
      (hKi.const_mul (2 * ((n + 1 : ℕ) : ℝ) ^ 2))) (hBi.const_mul 2),
    integral_add (hLi.const_mul 2) (hKi.const_mul (2 * ((n + 1 : ℕ) : ℝ) ^ 2)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    D.integral_hypersurface_bochner_slab hf hab hc hreg] at hle
  dsimp only at hle ⊢
  dsimp only [L] at hle
  linarith only [hle]

end PoincareConjecture.LeviCivitaData
