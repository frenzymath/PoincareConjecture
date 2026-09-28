import PoincareConjecture.Proofs.M04.CurvatureDerivativeHeat
import PoincareConjecture.Proofs.M04.CurvatureDerivativeHeatCorrectionGeneral
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem continuousOn_curvatureDerivativeNorm_time
    (F : RicciFlow n M J) (m : ℕ) (x : M) :
    ContinuousOn
      (fun t : ℝ ↦ (F.connection t).curvatureDerivativeNorm m x) J := by
  have hE := contMDiffOn_flow_curvatureDerivativeEnergy F m
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hsq : ContinuousOn
      (fun t : ℝ ↦ ((F.connection t).curvatureDerivativeNorm m x) ^ 2) J := by
    exact (hE.comp hslice.contMDiffOn (fun _ ht ↦ ⟨ht, mem_univ x⟩)).continuousOn
  have hsqrt := hsq.sqrt
  apply hsqrt.congr
  intro t ht
  change (F.connection t).curvatureDerivativeNorm m x =
    Real.sqrt (((F.connection t).curvatureDerivativeNorm m x) ^ 2)
  rw [Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (Real.sqrt_nonneg _)).symm

private theorem continuousOn_curvatureDerivativeNorm_zero_time
    (F : RicciFlow n M J) (x : M) :
    ContinuousOn
      (fun t : ℝ ↦ (F.connection t).curvatureDerivativeNorm 0 x) J :=
  continuousOn_curvatureDerivativeNorm_time F 0 x

private theorem continuousOn_curvatureDerivative_heat_rhs
    (F : RicciFlow n M J) (x : M) :
    ContinuousOn
      (fun t : ℝ ↦
        (F.connection t).laplacian
            (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x -
          2 * ((F.connection t).curvatureDerivativeNorm 2 x) ^ 2 +
          (196 * (n : ℝ) + 10 * (n : ℝ) ^ 7) *
            (F.connection t).curvatureDerivativeNorm 0 x *
              ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2) J := by
  have hE0 := contMDiffOn_flow_curvatureDerivativeEnergy F 0
  have hE1 := contMDiffOn_flow_curvatureDerivativeEnergy F 1
  have hE2 := contMDiffOn_flow_curvatureDerivativeEnergy F 2
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hq1 : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦
        ((F.connection p.1).curvatureDerivativeNorm 1 p.2) ^ 2)
      (J ×ˢ univ) := hE1
  have hLap := continuousOn_flow_timeDependentLaplacian F hq1
  have hLapx := hLap.comp hslice.continuous.continuousOn
    (fun _ ht ↦ ⟨ht, mem_univ x⟩)
  have hE1x : ContinuousOn
      (fun t : ℝ ↦ ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2) J :=
    (hE1.comp hslice.contMDiffOn (fun _ ht ↦ ⟨ht, mem_univ x⟩)).continuousOn
  have hE2x : ContinuousOn
      (fun t : ℝ ↦ ((F.connection t).curvatureDerivativeNorm 2 x) ^ 2) J :=
    (hE2.comp hslice.contMDiffOn (fun _ ht ↦ ⟨ht, mem_univ x⟩)).continuousOn
  have hN0 := continuousOn_curvatureDerivativeNorm_time F 0 x
  have hcoef : ContinuousOn
      (fun _ : ℝ ↦ 196 * (n : ℝ) + 10 * (n : ℝ) ^ 7) J := continuousOn_const
  have hLapx' : ContinuousOn
      (fun t : ℝ ↦
        (F.connection t).laplacian
          (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x) J := by
    rw [show
      ((fun p : ℝ × M ↦
          (F.connection p.1).laplacian
            (fun y ↦ ((F.connection p.1).curvatureDerivativeNorm 1 y) ^ 2) p.2) ∘
        (fun t : ℝ ↦ (t, x))) =
      (fun t : ℝ ↦
        (F.connection t).laplacian
          (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x) by
        funext t
        rfl] at hLapx
    exact hLapx
  have hprod : ContinuousOn
      (fun t : ℝ ↦
        (196 * (n : ℝ) + 10 * (n : ℝ) ^ 7) *
          (F.connection t).curvatureDerivativeNorm 0 x *
            ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2) J := by
    convert (hcoef.mul hN0).mul hE1x using 1
    ext t
    simp only [Pi.mul_apply]
  exact (hLapx'.sub (continuousOn_const.mul hE2x)).add hprod

theorem curvatureDerivative_heat_inequality
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J) (x : M) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm 2 x) ^ 2 +
      (196 * (n : ℝ) + 10 * (n : ℝ) ^ 7) *
        (F.connection t).curvatureDerivativeNorm 0 x *
          ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 := by
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hE1slice : ContDiffOn ℝ ∞
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2) J := by
    have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ ↦ (s, x)) := contMDiff_id.prodMk contMDiff_const
    exact (contMDiffOn_flow_curvatureDerivativeEnergy F 1).comp
      hslice.contMDiffOn (fun _ hs ↦ ⟨hs, mem_univ x⟩) |>.contDiffOn
  have hderivcont : ContinuousWithinAt
      (fun s ↦ derivWithin
        (fun q ↦ ((F.connection q).curvatureDerivativeNorm 1 x) ^ 2) J s)
      (interior J) t :=
    (hE1slice.continuousOn_derivWithin (uniqueDiffOn_convex hconv hne) (by simp))
      t ht |>.mono interior_subset
  have hRHScont :=
    (continuousOn_curvatureDerivative_heat_rhs F x t ht).mono interior_subset
  exact ContinuousWithinAt.closure_le (hdense ht) hderivcont hRHScont
    (fun s hs ↦ curvatureDerivative_heat_inequality_interior F hs x)

private theorem continuousOn_curvatureDerivative_heat_rhs_general
    (F : RicciFlow n M J) (m : ℕ) (x : M) :
    ContinuousOn
      (fun t : ℝ ↦
        (F.connection t).laplacian
            (fun y ↦ ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x -
          2 * ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2 +
          2 * (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
              (curvatureReactionWeight m : ℝ) *
              (F.connection t).curvatureDerivativeNorm m x *
                (∑ i ∈ Finset.range (m + 1),
                  (F.connection t).curvatureDerivativeNorm i x *
                    (F.connection t).curvatureDerivativeNorm (m - i) x) +
          2 * ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) *
              (F.connection t).curvatureDerivativeNorm 0 x *
                ((F.connection t).curvatureDerivativeNorm m x) ^ 2) J := by
  have hEm := contMDiffOn_flow_curvatureDerivativeEnergy F m
  have hEnext := contMDiffOn_flow_curvatureDerivativeEnergy F (m + 1)
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hLap := continuousOn_flow_timeDependentLaplacian F hEm
  have hLapx := hLap.comp hslice.continuous.continuousOn
    (fun _ ht ↦ ⟨ht, mem_univ x⟩)
  have hLapx' : ContinuousOn
      (fun t : ℝ ↦
        (F.connection t).laplacian
          (fun y ↦ ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x) J := by
    rw [show
      ((fun p : ℝ × M ↦
          (F.connection p.1).laplacian
            (fun y ↦ ((F.connection p.1).curvatureDerivativeNorm m y) ^ 2) p.2) ∘
        (fun t : ℝ ↦ (t, x))) =
      (fun t : ℝ ↦
        (F.connection t).laplacian
          (fun y ↦ ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x) by
        funext t
        rfl] at hLapx
    exact hLapx
  have hEmx : ContinuousOn
      (fun t : ℝ ↦ ((F.connection t).curvatureDerivativeNorm m x) ^ 2) J :=
    (hEm.comp hslice.contMDiffOn (fun _ ht ↦ ⟨ht, mem_univ x⟩)).continuousOn
  have hEnextx : ContinuousOn
      (fun t : ℝ ↦ ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2) J :=
    (hEnext.comp hslice.contMDiffOn (fun _ ht ↦ ⟨ht, mem_univ x⟩)).continuousOn
  have hNorm (j : ℕ) : ContinuousOn
      (fun t : ℝ ↦ (F.connection t).curvatureDerivativeNorm j x) J :=
    continuousOn_curvatureDerivativeNorm_time F j x
  have hSum : ContinuousOn
      (fun t : ℝ ↦ ∑ i ∈ Finset.range (m + 1),
        (F.connection t).curvatureDerivativeNorm i x *
          (F.connection t).curvatureDerivativeNorm (m - i) x) J := by
    apply continuousOn_finsetSum
    intro i hi
    exact (hNorm i).mul (hNorm (m - i))
  have hA : ContinuousOn
      (fun _ : ℝ ↦ 2 * (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (curvatureReactionWeight m : ℝ)) J := continuousOn_const
  have hB : ContinuousOn
      (fun _ : ℝ ↦ 2 * ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6)) J :=
    continuousOn_const
  have hLower : ContinuousOn
      (fun t : ℝ ↦
        2 * (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
            (curvatureReactionWeight m : ℝ) *
            (F.connection t).curvatureDerivativeNorm m x *
              (∑ i ∈ Finset.range (m + 1),
                (F.connection t).curvatureDerivativeNorm i x *
                  (F.connection t).curvatureDerivativeNorm (m - i) x)) J := by
    exact (hA.mul (hNorm m)).mul hSum
  have hUpper : ContinuousOn
      (fun t : ℝ ↦
        2 * ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) *
            (F.connection t).curvatureDerivativeNorm 0 x *
              ((F.connection t).curvatureDerivativeNorm m x) ^ 2) J := by
    exact (hB.mul (hNorm 0)).mul hEmx
  exact ((hLapx'.sub (continuousOn_const.mul hEnextx)).add hLower).add hUpper

theorem curvatureDerivative_heat_inequality_general
    (F : RicciFlow n M J) (m : ℕ) {t : ℝ} (ht : t ∈ J) (x : M) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2 +
      2 * (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (curvatureReactionWeight m : ℝ) *
        (F.connection t).curvatureDerivativeNorm m x *
          (∑ i ∈ Finset.range (m + 1),
            (F.connection t).curvatureDerivativeNorm i x *
            (F.connection t).curvatureDerivativeNorm (m - i) x) +
      2 * ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) *
        (F.connection t).curvatureDerivativeNorm 0 x *
        ((F.connection t).curvatureDerivativeNorm m x) ^ 2 := by
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hEmSlice : ContDiffOn ℝ ∞
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2) J := by
    have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ ↦ (s, x)) := contMDiff_id.prodMk contMDiff_const
    exact (contMDiffOn_flow_curvatureDerivativeEnergy F m).comp
      hslice.contMDiffOn (fun _ hs ↦ ⟨hs, mem_univ x⟩) |>.contDiffOn
  have hderivcont : ContinuousWithinAt
      (fun s ↦ derivWithin
        (fun q ↦ ((F.connection q).curvatureDerivativeNorm m x) ^ 2) J s)
      (interior J) t :=
    (hEmSlice.continuousOn_derivWithin (uniqueDiffOn_convex hconv hne) (by simp))
      t ht |>.mono interior_subset
  have hRHScont :=
    (continuousOn_curvatureDerivative_heat_rhs_general F m x t ht).mono interior_subset
  exact ContinuousWithinAt.closure_le (hdense ht) hderivcont hRHScont
    (fun s hs ↦ curvatureDerivative_heat_inequality_interior_general F m hs x)

end PoincareConjecture.M04
