import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth extensions preserving germs along a closed subset

Mathlib's smooth separation theorem produces a cutoff equal to one near
the closed subset and zero near the complement of the smooth domain.
The resulting extension preserves endpoint derivatives of the radial
curves used in Morgan--Tian, Remark 19.42, p. 472. See the closed-corner
ray derivation for the application and the totalization checks.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareMT

/-- A map smooth on an open set has a globally smooth representative with
the same germ at every point of a closed subset. The cutoff is supplied by
Mathlib's smooth Urysohn theorem; no regularity is required outside `U`.
This preserves the endpoint jets needed in MT Remark 19.42, p. 472. -/
theorem m64_exists_contDiff_eq_nhds_of_isClosed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {f : E → F} {K U : Set E}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ n f U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨chi, hzero, hone, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
      hU.isClosed_compl hK
      (show Disjoint Uᶜ K from disjoint_left.mpr (fun _ hx hk => hx (hKU hk)))
      (n := n)
  refine ⟨fun x => chi x • f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact chi.contMDiff.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in 𝓝 x, chi y = 0 := hzero.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      exact hy ▸ zero_smul ℝ (f y)
  · intro x hx
    have ho : ∀ᶠ y in 𝓝 x, chi y = 1 := hone.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [ho] with y hy
    exact hy ▸ one_smul ℝ (f y)

end PoincareMT
