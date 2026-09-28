import PoincareConjecture.Proofs.M64.Mathlib.SmoothClosedExtension
import PoincareConjecture.Proofs.M64.Mathlib.TranslatedLpConvergence














noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "X" => EuclideanSpace ℝ (Fin d)





theorem m64_exists_contDiff_inward_approximation
    {O K : Set X} (hO : IsOpen O) (hK : IsClosed K)
    {u : X → E} (hs : ContDiffOn ℝ 1 u O)
    (hu : MemLp u 2 (volume.restrict O))
    (hD : ∀ i : Fin d, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict O))
    {h : ℕ → X} {a : X} (hh : Tendsto h atTop (𝓝 a))
    (hbase : ∀ᵐ x ∂volume.restrict K, x + a ∈ O)
    (hshift : ∀ j, MapsTo (fun x => x + h j) K O) :
    ∃ f : ℕ → X → E, (∀ j, ContDiff ℝ 1 (f j)) ∧
      (∀ j x, x ∈ K → f j =ᶠ[𝓝 x] fun y => u (y + h j)) ∧
      Tendsto (fun j => eLpNorm (fun x => f j x - u (x + a))
        2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun j => eLpNorm (fun x =>
        fderiv ℝ (f j) x (EuclideanSpace.single i 1) -
          fderiv ℝ u (x + a) (EuclideanSpace.single i 1))
            2 (volume.restrict K)) atTop (𝓝 0) := by
  have hex (j : ℕ) : ∃ f : X → E, ContDiff ℝ 1 f ∧
      ∀ x ∈ K, f =ᶠ[𝓝 x] fun y => u (y + h j) := by
    apply m64_exists_contDiff_eq_nhds_of_isClosed hK
      (hO.preimage (continuous_id.add continuous_const)) (hshift j)
    exact hs.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hx => hx)
  choose f hf hmatch using hex
  refine ⟨f, hf, hmatch, ?_, ?_⟩
  · have hlim := m64MemLp_add_restrict_tendsto hO.measurableSet hK.measurableSet
      hu hh hbase hshift
    apply hlim.congr
    intro j
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [(hmatch j x hx).self_of_nhds]
  · intro i
    have hlim := m64MemLp_add_restrict_tendsto hO.measurableSet hK.measurableSet
      (hD i) hh hbase hshift
    apply hlim.congr
    intro j
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [(hmatch j x hx).fderiv_eq, fderiv_comp_add_right]

end PoincareConjecture
