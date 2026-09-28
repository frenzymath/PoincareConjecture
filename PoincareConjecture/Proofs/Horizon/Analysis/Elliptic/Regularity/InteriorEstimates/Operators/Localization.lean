import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Coefficients

noncomputable section

open Set Filter Topology
open scoped ContDiff
open Poincare.Analysis.Sobolev.NirenbergEuclidean

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_smooth_extension_on_precompact
    {O V : Set E} (hO : IsOpen O) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ EqOn v u V := by
  obtain ⟨χ, hχ, _, _, hχone, hχsupp⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc hO hVO
  refine ⟨fun x => χ x * u x, contDiff_cutoff_mul hO hχ hu hχsupp, ?_⟩
  intro x hx
  simp only [hχone x (subset_closure hx), one_mul]

theorem exists_secondOrderOperator_extension [NeZero d]
    {O V : Set E} (hO : IsOpen O) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → E → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hpos : ∀ x ∈ O, (a x).PosDef)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) O) :
    ∃ (B : SmoothEllipticBilinearForm d univ) (b' : Fin d → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (b' i)) ∧ EqOn B.a a V ∧ (∀ i, EqOn (b' i) (b i) V) := by
  obtain ⟨U, _, hVU, _, _, B, hBa, _⟩ :=
    exists_global_elliptic_extension hO hVc hVO a (fun _ => 0)
      ha hpos contDiffOn_const
  choose b' hb' heq using fun i => exists_smooth_extension_on_precompact hO hVc hVO (hb i)
  exact ⟨B, b', hb', hBa.mono (subset_closure.trans hVU), heq⟩

end Poincare.Analysis.Elliptic.InteriorEstimates
