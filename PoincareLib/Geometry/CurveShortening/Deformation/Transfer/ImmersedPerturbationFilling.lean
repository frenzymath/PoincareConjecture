import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.AreaContinuity.ConstantLift
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.PeriodicSpeed
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Actual fillings along the perturbation parameter path

The literal radial parameter path gives a globally smooth periodic
annulus after the fixed smooth transition. Its exact endpoint maps
allow the actual M64 forward gluing theorem to transport each original
disk, with its arbitrary carried boundary homeomorphism unchanged.
MT Lemma 19.4, pp. 439-441; M65 derivation 49, section 14.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace PoincareMT.M65Perturbation

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b circumference delta : ℝ} {J : Set ℝ}
  {F : RicciFlow 3 M (Icc a b)}

/-- The actual radial parameter path, smoothly made constant outside
the unit interval. MT Lemma 19.4; derivation 49, section 14. -/
def parameterAnnulusMap (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
    (p : Fin N → ℝ) (q : ℝ) (z : LoopPlane) : M :=
  periodicFreeLoop (Gamma (Real.smoothTransition (z 1) • p) q) (z 0)

/-- The entire displayed annulus stays inside the proved parameter
ball, so its global smoothness follows from the actual family.
MT Lemma 19.4; derivation 49, section 14. -/
theorem parameterAnnulusMap_contMDiff
    (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
    (hGamma : ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)))
    {p : Fin N → ℝ} (hp : p ∈ ball 0 delta) {q : ℝ} (hq : q ∈ J) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (parameterAnnulusMap Gamma p q) := by
  have hmap : ContDiff ℝ ∞ (fun z : LoopPlane =>
      (Real.smoothTransition (z 1) • p, (z 0, q))) := by fun_prop
  apply hGamma.comp_contMDiff hmap.contMDiff
  intro z
  refine ⟨?_, mem_univ _, hq⟩
  have hnorm : ‖Real.smoothTransition (z 1) • p‖ ≤ ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
  simpa only [mem_ball, dist_zero_right] using
    hnorm.trans_lt (by simpa only [mem_ball, dist_zero_right] using hp)

/-- Genuine forward disk gluing along the actual parameter path.
The lower loop is identified by its actual angular values, and the
conclusion retains the literal annular area and arbitrary positive
slack. MT Lemma 19.4; derivation 49, section 14. -/
theorem parameter_filling (P : M62.CircleProductData F circumference)
    (q : ℝ) (disks : M64DiskAreaComparison P q)
    (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
    (hGamma : ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)))
    {p : Fin N → ℝ} (hp : p ∈ ball 0 delta) (hq : q ∈ J)
    (gamma : C1FreeLoopSpace (M := M))
    (hbase : ∀ x, periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop gamma x)
    (D0 : LipschitzSpanningDisk (F.metric q) gamma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Dp : LipschitzSpanningDisk (F.metric q) (Gamma p q),
      Dp.area ≤ D0.area + m64AnnulusArea (F.metric q) (parameterAnnulusMap Gamma p q) +
        epsilon := by
  have hf := (parameterAnnulusMap_contMDiff Gamma hGamma hp hq).of_le
    (show (1 : ℕ∞) ≤ ∞ by simp)
  have hperiodic (x y : ℝ) :
      parameterAnnulusMap Gamma p q (annulusPoint (x + curvePeriod) y) =
        parameterAnnulusMap Gamma p q (annulusPoint x y) := by
    exact Proofs.M58.periodic_periodicFreeLoop (Gamma (Real.smoothTransition y • p) q) x
  have hzero (x : ℝ) : parameterAnnulusMap Gamma p q (annulusPoint x 0) =
      periodicFreeLoop gamma x := by
    change periodicFreeLoop (Gamma (Real.smoothTransition 0 • p) q) x = _
    simpa only [Real.smoothTransition.zero, zero_smul] using hbase x
  have hone (x : ℝ) : parameterAnnulusMap Gamma p q (annulusPoint x 1) =
      periodicFreeLoop (Gamma p q) x := by
    change periodicFreeLoop (Gamma (Real.smoothTransition 1 • p) q) x = _
    rw [Real.smoothTransition.one, one_smul]
  let A := m65ConstantCircleAnnulus P q (parameterAnnulusMap Gamma p q)
    hf hperiodic hzero hone
  exact (disks _ _ A gamma (Gamma p q) (fun _ => rfl) (fun _ => rfl)).forward
    epsilon hepsilon D0

end PoincareMT.M65Perturbation
