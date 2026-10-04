import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.FillingArea.Curvature
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Conformal.Ricci

/-!
# The literal supplied-disk Gauss--Bonnet input

This geometric input is separate from attainment and from the actual
time-variation theorem. It retains both genuine integrabilities and
the actual curvature flux. MT Lemma 19.2 and Claim 19.5, pp. 438-441;
M65 derivations 45, supplied-disk GB and filling comparison.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareMT

/-- The geometric Gauss-contraction consequence for an actual supplied
minimal disk. The arbitrary ambient section is constrained only on
the genuine loop; no variation or filling inequality is assumed.
MT Lemma 19.2, pp. 438-441; derivation 45. -/
def M65SuppliedDiskGaussBonnet {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) : Prop :=
  ∀ (gamma : C1FreeLoopSpace (M := M)) (S : M65MinimalDisk g D gamma),
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma) →
    (∀ x, curveVelocity (n := 3) (periodicFreeLoop gamma) x ≠ 0) →
    Function.Injective (gamma : LoopCircle → M) →
    ∀ H : (p : M) → TangentSpace (𝓡 3) p,
      (∀ x, H (periodicFreeLoop gamma x) = M65Filling.loopCurvature D gamma x) →
      let Q := fun z => m65PlaneRicciTraceDensity D S.disk.map z -
        D.scalarCurvature (S.disk.map z) * m60AreaDensity g S.disk.map z / 2
      let B := fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
        (H (S.disk.map (Proofs.M58.angularPoint theta)))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
          (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
      IntegrableOn Q loopDiskSet volume ∧
        IntervalIntegrable B volume (-Real.pi) Real.pi ∧
        2 * Real.pi ≤ (∫ z in loopDiskSet, Q z) -
          ∫ theta in (-Real.pi)..Real.pi, B theta

end PoincareMT
