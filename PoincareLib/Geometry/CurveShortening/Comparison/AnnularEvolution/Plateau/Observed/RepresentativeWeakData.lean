import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Observed.LowerHolder
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Weak.Classical

/-! The observed Holder representative keeps the original reflected
weak columns. Source: Morrey ICM pp. 183-185; M64 finite-boundary-
regularity derivation, almost-everywhere representative transport.
Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open Poincare.Analysis.Sobolev.Weak

namespace PoincareMT.M64ObservedWeakAnnulus

/-- Any genuine representative of the observed reflection has the same literal L2 weak
columns on the original open neighborhood. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449. -/
theorem lower_representative_weak_data {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (hsub : O ⊆ m64AnnulusLowerDomain)
    {U : LoopPlane → EuclideanSpace ℝ (Fin m)}
    (hae : U =ᵐ[volume.restrict O] A.lowerReflectedValue) :
    MemLp U 2 (volume.restrict O) ∧
      (∀ i, MemLp (A.lowerReflectedColumn i) 2 (volume.restrict O)) ∧
      ∀ i j, HasWeakPartialDeriv i (fun p => A.lowerReflectedColumn i p j)
        (fun p => U p j) O := by
  refine ⟨((A.lower_reflected_memLp.1).mono_measure
    (Measure.restrict_mono_set volume hsub)).ae_eq hae.symm, ?_, ?_⟩
  · exact fun i => (A.lower_reflected_memLp.2 i).mono_measure
      (Measure.restrict_mono_set volume hsub)
  · intro i j
    exact M60.suWeakPartial_congr_ae ((A.lower_reflected_weak i j).restrict hO hsub)
      (hae.mono fun p hp => congrArg (fun y : EuclideanSpace ℝ (Fin m) => y j) hp)
      (Eventually.of_forall fun _ => rfl)

end PoincareMT.M64ObservedWeakAnnulus
