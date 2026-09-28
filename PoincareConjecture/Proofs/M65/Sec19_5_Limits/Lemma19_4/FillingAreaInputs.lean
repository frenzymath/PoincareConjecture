import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaCurvature
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalRicci










set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture





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

end PoincareConjecture
