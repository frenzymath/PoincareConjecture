import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Basic







noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)


theorem memWkp_succ_of_weakDerivatives
    {Ω : Set E} (hΩ : IsOpen Ω) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : E → ℝ} {g : Fin d → E → ℝ} {k : ℕ}
    (hu : MemLp u p (volume.restrict Ω))
    (hg : ∀ i, MemWkp k p (g i) Ω)
    (hweak : ∀ i, Weak.HasWeakPartialDeriv i (g i) u Ω) :
    MemWkp (k + 1) p u Ω := by
  have hu1 : Weak.MemW1p p u Ω :=
    ⟨hu, fun i => ⟨g i, (hg i).memLp, hweak i⟩⟩
  refine ⟨hu1, fun i => ?_⟩
  have hae : chosenWeakPartial' p i u Ω =ᵐ[volume.restrict Ω] g i :=
    Weak.HasWeakPartialDeriv.ae_eq hΩ
      (chosenWeakPartial'_isWeakPartial_of_mem hu1 i) (hweak i)
      ((chosenWeakPartial'_memLp_of_mem hu1 i).locallyIntegrable hp)
      ((hg i).memLp.locallyIntegrable hp)
  exact (MemWkp_congr_ae hp hΩ hae).mpr (hg i)


theorem memWkp_succ_iff_exists_weakDerivatives
    {Ω : Set E} (hΩ : IsOpen Ω) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : E → ℝ} {k : ℕ} :
    MemWkp (k + 1) p u Ω ↔
      MemLp u p (volume.restrict Ω) ∧
        ∃ g : Fin d → E → ℝ,
          (∀ i, MemWkp k p (g i) Ω) ∧
          (∀ i, Weak.HasWeakPartialDeriv i (g i) u Ω) := by
  constructor
  · intro hu
    exact ⟨hu.memLp, fun i => chosenWeakPartial' p i u Ω,
      hu.chosenWeakPartial_mem, fun i =>
        chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i⟩
  · rintro ⟨hu, g, hg, hweak⟩
    exact memWkp_succ_of_weakDerivatives hΩ hp hu hg hweak

end Poincare.Analysis.Sobolev.Euclidean
