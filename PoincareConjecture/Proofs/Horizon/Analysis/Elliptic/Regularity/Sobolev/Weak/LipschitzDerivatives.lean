import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Lipschitz








noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Poincare.Analysis.Sobolev.Weak

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem memLp_top_fderiv_apply_of_lipschitzOn
    {u : E → ℝ} {O : Set E} {C : ℝ≥0}
    (hO : IsOpen O) (hu : LipschitzOnWith C u O) (w : E) :
    MemLp (fun x => fderiv ℝ u x w) ∞ (volume.restrict O) := by
  obtain ⟨v, hv, heq⟩ := hu.extend_real
  refine (memLp_congr_ae ?_).mp (hv.memLp_lineDeriv (μ := volume.restrict O) w)
  filter_upwards [ae_restrict_mem hO.measurableSet,
    ae_restrict_of_ae (hv.ae_differentiableAt (μ := volume))] with x hx hdx
  have hnear : u =ᶠ[𝓝 x] v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact heq hy
  rw [hdx.lineDeriv_eq_fderiv, hnear.fderiv_eq]

end Poincare.Analysis.Sobolev.Weak
