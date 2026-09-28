import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Fields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [IsManifold (𝓡 (m + 2)) ∞ M]
  {g : RiemannianMetric (m + 2) M}

theorem integral_regularLevel_scalarCurvature_posPart_div_speed_le
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t α : ℝ} (ht : t ∈ I) (hα : 0 < α)
    (hspeed : ∀ x, f x = t → 1 / α ≤ g.tangentNorm x (g.gradient f x)) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
    letI := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
    let DL := (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) t g).leviCivitaData
    (∫ z, max 0 (DL.scalarCurvature z) /
      g.tangentNorm (openLevelIncl f U t z) (g.gradient f (openLevelIncl f U t z))
      ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
      α * (∫ z, max 0 (DL.scalarCurvature z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) := by
  let U := g.regularDomain hf
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
  letI := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
  let DL := (RiemannianMetric.regularLevelMetric
    hf U (g.regularDomain_regular hf) t g).leviCivitaData
  let S := fun x => D.scalarCurvature x -
    2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) + D.levelGaussTerm f x
  have hUq : (U : Set M) ⊆ {x | 0 < D.levelQ f x} := by
    intro x hx
    exact Real.sqrt_pos.mp hx
  have hSc : ContinuousOn S U :=
    (D.continuous_scalarCurvature.continuousOn.sub
      ((D.continuousOn_ricci_levelUnitNormal hf).mono hUq |>.const_mul 2)).add
      ((D.continuousOn_levelGaussTerm hf).mono hUq)
  have hSpos : ContinuousOn (fun x => max 0 (S x)) U :=
    (continuousOn_const (c := (0 : ℝ))).sup hSc
  have hSquot : ContinuousOn
      (fun x => max 0 (S x) / g.tangentNorm x (g.gradient f x)) U :=
    hSpos.div (g.continuous_tangentNorm_gradient hf).continuousOn
      (fun _ hx => ne_of_gt hx)
  have hiS := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht hSpos
  have hiW := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht hSquot
  dsimp only [Function.comp_def] at hiS hiW
  have hbound := integral_mono hiW (hiS.const_mul α) (fun z => by
    have hs : 0 < g.tangentNorm (openLevelIncl f U t z)
        (g.gradient f (openLevelIncl f U t z)) := z.1.2
    have hslow := (div_le_iff₀ hα).mp (hspeed (openLevelIncl f U t z) z.2)
    have hinv : 1 / g.tangentNorm (openLevelIncl f U t z)
        (g.gradient f (openLevelIncl f U t z)) ≤ α :=
      (div_le_iff₀ hs).mpr (by nlinarith only [hslow])
    calc
      _ = max 0 (S (openLevelIncl f U t z)) *
          (1 / g.tangentNorm (openLevelIncl f U t z)
            (g.gradient f (openLevelIncl f U t z))) := by ring
      _ ≤ max 0 (S (openLevelIncl f U t z)) * α :=
        mul_le_mul_of_nonneg_left hinv (le_max_left _ _)
      _ = _ := mul_comm _ _)
  rw [integral_const_mul] at hbound
  have hscalar (z : openLevelSet f U t) : DL.scalarCurvature z = S (openLevelIncl f U t z) :=
    D.regularLevel_scalarCurvature_gauss g hf U (g.regularDomain_regular hf) t DL z
  change (∫ z, max 0 (DL.scalarCurvature z) /
      g.tangentNorm (openLevelIncl f U t z) (g.gradient f (openLevelIncl f U t z))
      ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
    α * (∫ z, max 0 (DL.scalarCurvature z)
      ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)
  simp_rw [hscalar]
  exact hbound

theorem integral_regularLevel_scalarCurvature_posPart_le_of_induction
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t α β C : ℝ} (ht : t ∈ I) (hα : 0 < α) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hhess : ∀ x, f x = t → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ β * g.inner x v v)
    (hspeed : ∀ x, f x = t →
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
    letI := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
    let DL := (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) t g).leviCivitaData
    ((∫ z, max 0 (DL.scalarCurvature z)
      ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
        C * (1 + ∫ z, D.levelSectionalError f K β (openLevelIncl f U t z)
          ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)) →
    (∫ z, max 0 (DL.scalarCurvature z) /
      g.tangentNorm (openLevelIncl f U t z) (g.gradient f (openLevelIncl f U t z))
      ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
      α * C * (1 + (∫ z, K (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) +
        ((m + 1 : ℕ) : ℝ) * (1 + α) * β ^ 2 * g.regularLevelArea hf t -
          β * deriv (g.regularLevelArea hf) t) := by
  dsimp only
  intro hind
  have hweight := D.integral_regularLevel_scalarCurvature_posPart_div_speed_le
    hf hI hproper hreg ht hα (fun x hx => (hspeed x hx).1)
  have herror := D.integral_levelSectionalError_le
    hf hI hproper hreg ht hα hβ hKc hhess hspeed
  have hind' := mul_le_mul_of_nonneg_left hind hα.le
  have herror' := mul_le_mul_of_nonneg_left (add_le_add_left herror 1)
    (mul_nonneg hα.le hC)
  dsimp only at hweight
  nlinarith only [hweight, hind', herror']

end PoincareConjecture.LeviCivitaData
