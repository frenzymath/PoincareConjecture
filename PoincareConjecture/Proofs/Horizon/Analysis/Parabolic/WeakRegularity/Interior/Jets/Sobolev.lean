import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.FullCanonicalJet
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Coordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Basic

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical Sobolev.BoundaryCoordinates Sobolev.Euclidean Sobolev.Weak

variable {n : ℕ}

private def splitDirection (i : Fin (n + 1)) : Fin (n + 1) :=
  Fin.cases (Fin.last n) Fin.castSucc i

private theorem split_single (i : Fin (n + 1)) :
    split n (EuclideanSpace.single i 1) = canonicalDirection (splitDirection i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [splitDirection, Fin.cases_zero, canonicalDirection_last]
    apply Prod.ext
    · ext j
      simp [EuclideanSpace.single_apply]
    · simp [EuclideanSpace.single_apply]
  · simp only [splitDirection, Fin.cases_succ, canonicalDirection_castSucc, spatialDirection]
    apply Prod.ext
    · ext j
      simp [EuclideanSpace.single_apply]
    · simp [EuclideanSpace.single_apply]

private theorem weakPartial_comp_split
    {U : Set (Spacetime n)} (hU : IsOpen U) {u g : Spacetime n → ℝ}
    (i : Fin (n + 1))
    (hg : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y in U, φ y * g y) =
        -(∫ y in U, fderiv ℝ φ y (canonicalDirection (splitDirection i)) * u y)) :
    HasWeakPartialDeriv i (g ∘ split n) (u ∘ split n) ((split n) ⁻¹' U) := by
  intro ψ hψ hψc hψU
  let φ : Spacetime n → ℝ := ψ ∘ (split n).symm
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (split n).symm.contDiff
  have hφc : HasCompactSupport φ := hψc.comp_homeomorph (split n).symm.toHomeomorph
  have hφU : tsupport φ ⊆ U := by
    intro y hy
    have hy' : (split n).symm y ∈ tsupport ψ := by
      exact (tsupport_comp_subset_preimage ψ (split n).symm.continuous) hy
    simpa using hψU hy'
  have hd (x : EuclideanSpace ℝ (Fin (n + 1))) :
      fderiv ℝ φ (split n x) (canonicalDirection (splitDirection i)) =
        fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    rw [← split_single]
    have hh := ((hψ.differentiable (by simp) ((split n).symm (split n x))).hasFDerivAt.comp
      (split n x) (split n).symm.hasFDerivAt)
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L => L (split n (EuclideanSpace.single i 1))) hh.fderiv
  have hmp : MeasurePreserving (split n) (volume.restrict ((split n) ⁻¹' U))
      (volume.restrict U) :=
    (measurePreserving_split n).restrict_preimage hU.measurableSet
  have he := hg φ hφ hφc hφU
  rw [← hmp.integral_comp (split n).toHomeomorph.measurableEmbedding
      (fun y => φ y * g y),
    ← hmp.integral_comp (split n).toHomeomorph.measurableEmbedding
      (fun y => fderiv ℝ φ y (canonicalDirection (splitDirection i)) * u y)] at he
  simp only [φ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, hd] at he
  simp only [Function.comp_apply, mul_comm] at he ⊢
  linarith

theorem HasCanonicalL2Jet.memWkp_comp_split
    {U : Set (Spacetime n)} (hU : IsOpen U) {k : ℕ} {u : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U k u) :
    MemWkp k 2 (u ∘ split n) ((split n) ⁻¹' U) := by
  have hV : IsOpen ((split n) ⁻¹' U) := hU.preimage (split n).continuous
  have hmp := (measurePreserving_split n).restrict_preimage hU.measurableSet
  induction k generalizing u with
  | zero => exact hu.comp_measurePreserving hmp
  | succ k ih =>
    obtain ⟨hum, g, hg, hgw⟩ := hu
    have hpartial (i : Fin (n + 1)) := weakPartial_comp_split hU i (hgw (splitDirection i))
    have hgLp (i : Fin (n + 1)) :
        MemLp (g (splitDirection i) ∘ split n) 2 (volume.restrict ((split n) ⁻¹' U)) :=
      (hg (splitDirection i)).memLp.comp_measurePreserving hmp
    have hW : MemW1p 2 (u ∘ split n) ((split n) ⁻¹' U) :=
      ⟨hum.comp_measurePreserving hmp, fun i => ⟨_, hgLp i, hpartial i⟩⟩
    refine ⟨hW, fun i => ?_⟩
    have heq := HasWeakPartialDeriv.ae_eq hV
      (chosenWeakPartial'_isWeakPartial_of_mem hW i) (hpartial i)
      ((chosenWeakPartial'_memLp_of_mem hW i).locallyIntegrable (by norm_num))
      ((hgLp i).locallyIntegrable (by norm_num))
    exact (MemWkp_congr_ae (by norm_num) hV heq).mpr (ih (hg (splitDirection i)))

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
