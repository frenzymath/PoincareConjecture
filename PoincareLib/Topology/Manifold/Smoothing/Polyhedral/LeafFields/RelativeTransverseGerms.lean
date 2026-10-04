import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.LeafFields.RelativeTransverseSmoothing
import Mathlib.Topology.Separation.Regular

/-!
# Relative transverse smoothing preserving whole germs

Fix a closed neighborhood of the prescribed relative set during
smooth approximation. The resulting normalized transverse field
agrees with the old field on a neighborhood of that set, as needed
for Cairns' ambient gluing, pp. 804--805. See M76 derivation 57.
-/

set_option autoImplicit false

open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Relative smoothing may retain the whole germ near a closed
relative set, while preserving normalization and transversality
on a compact control set. See Cairns p. 804 and M76 derivation 57. -/
theorem Continuous.exists_contDiff_frameTransverse_eventuallyEq
    {f : X → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ x, Function.RightInverse J (f x)) (n : ℕ∞)
    {C S U : Set X} (hC : IsCompact C) (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContDiffOn ℝ n f U) (A : Set E)
    (htrans : ∀ x ∈ C, (f x).ker.IsSecantTransverse A) :
    ∃ g : X → E →L[ℝ] F, ContDiff ℝ n g ∧
      (∀ x, Function.RightInverse J (g x)) ∧ g =ᶠ[𝓝ˢ S] f ∧
      ∀ x ∈ C, (g x).ker.IsSecantTransverse A := by
  obtain ⟨O, hO, hSO, hOU⟩ := mem_nhdsSet_iff_exists.mp hU
  obtain ⟨D, hDS, hD, hDO⟩ := exists_mem_nhdsSet_isClosed_subset
    (hO.mem_nhdsSet.mpr hSO) hS
  obtain ⟨g, hg, hgn, hgeq, hgt⟩ := hf.exists_contDiff_frameTransverse_eqOn J hframe n
    hC hD (hO.mem_nhdsSet.mpr hDO) (hfU.mono hOU) A htrans
  exact ⟨g, hg, hgn, Filter.mem_of_superset hDS (fun x hx => hgeq hx), hgt⟩
