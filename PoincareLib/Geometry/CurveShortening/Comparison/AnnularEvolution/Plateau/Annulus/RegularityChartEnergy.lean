import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.RegularityInverseChart
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.ReplacementEnergy

/-!
# Exact weak columns and energy in an annular target chart

Weak derivative uniqueness identifies the inverse-chart columns of the
original map. The observation metric on those columns is exactly the
pullback coordinate metric; no classical differentiability of the map is
used in either statement.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

/-- Weak derivative uniqueness identifies the actual L2 columns of equal maps. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64WeakColumns_ae_eq {m : ℕ} {O : Set LoopPlane} (hO : IsOpen O)
    {u v : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {W V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) O)
    (hv : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => v p j) O)
    (heq : u =ᵐ[volume.restrict O] v) :
    ∀ i, W i =ᵐ[volume.restrict O] V i := by
  intro i
  have hcoord (j : Fin m) : (fun p => W i p j) =ᵐ[volume.restrict O]
      (fun p => V i p j) := by
    have h := m64WeakPartialDeriv_ae_congr
      (heq.mono fun p hp => congrArg (fun x : EuclideanSpace ℝ (Fin m) => x j) hp)
      (Eventually.of_forall fun _ => rfl) (hw i j)
    exact HasWeakPartialDeriv.ae_eq hO h (hv i j)
      (((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (hW i)).locallyIntegrable (by norm_num))
      (((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (hV i)).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.mpr hcoord] with p hp
  exact PiLp.ext hp

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The observed quadratic form of inverse-chart columns is the actual pullback metric.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64InverseChart_observed_metric
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (b : M) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) b).target)
    (v : EuclideanSpace ℝ (Fin n)) :
    Q ((extChartAt (𝓡 n) b).symm y)
        (fderiv ℝ (e ∘ (extChartAt (𝓡 n) b).symm) y v)
        (fderiv ℝ (e ∘ (extChartAt (𝓡 n) b).symm) y v) =
      g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y v v := by
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) b y hy).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)
  have hd := mfderiv_comp y ((he _).mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  rw [hd]
  exact hQ _ _

end PoincareMT
