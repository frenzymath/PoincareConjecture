import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.SupportedFinitePLExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Isotopy.SmallSupportedPLIsotopy
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexPolyhedralNeighborhood

/-!
# Ambient isotopies realizing finite PL displacement data

Extend the prescribed values with support in a chosen neighborhood,
then apply the quantitative small-displacement isotopy theorem.
See Alexander 1924, p. 7, Hudson 1969, pp. 15--19 and
M76 derivation 144.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Finite PL displacement data inside a convex finite carrier
are realized for small signed times by an ambient isotopy fixing
the complement of any specified open neighborhood of the data.
Its carrier restrictions remain finite PL. See derivation 144. -/
theorem FinitePiecewiseAffineOn.exists_supported_isotopy_extension
    {f : E → E} {S U : Set E} (hf : FinitePiecewiseAffineOn f S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hcv : Convex ℝ K.space)
    (hSK : S ⊆ interior K.space) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
      Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
      Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
      (∀ (t : Icc (-ε) ε) (x : E), (t : ℝ) = 0 → H t x = x) ∧
      (∀ (t : Icc (-ε) ε) (x : E), x ∈ S → H t x = x + (t : ℝ) • f x) ∧
      ∀ t : Icc (-ε) ε, (∀ x, x ∉ U → H t x = x) ∧
        (∀ x, x ∉ interior K.space → H t x = x) ∧ H t '' K.space = K.space ∧
        ∃ e : K.space ≃ₜ K.space, e.IsFinitePL ∧ ∀ x : K.space, (e x : E) = H t x := by
  obtain ⟨g, hg, hgf, hgzero, _⟩ := hf.exists_supported_extension K hK
    (hSK.trans interior_subset) (hU.inter isOpen_interior) (subset_inter hSU hSK)
  have hfront : ∀ x ∈ frontier K.space, g x = 0 := by
    intro x hx
    exact hgzero x (fun hi => hx.2 hi.2)
  obtain ⟨ε, hε, H, hc, hci, hformula, hrest⟩ :=
    hg.exists_small_supported_isotopy hcv hfront
  refine ⟨ε, hε, H, hc, hci, ?_, ?_, fun t => ⟨?_, hrest t⟩⟩
  · intro t x ht
    rw [hformula, ht, zero_smul, add_zero]
  · intro t x hx
    rw [hformula, indicator_of_mem (interior_subset (hSK hx)), hgf hx]
  · intro x hx
    rw [hformula]
    have hz : K.space.indicator g x = 0 := by
      by_cases hxK : x ∈ K.space
      · rw [indicator_of_mem hxK]
        exact hgzero x (fun hi => hx hi.1)
      · exact indicator_of_notMem hxK g
    rw [hz, smul_zero, add_zero]

/-- Compact finite PL displacement data admit a supported
ambient isotopy with an internally constructed convex carrier.
The support neighborhood is arbitrary; only the time interval
shrinks with the data. See Alexander p. 7 and derivation 144. -/
theorem FinitePiecewiseAffineOn.exists_supported_ambient_isotopy
    {f : E → E} {S U : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
      Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
      Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
      (∀ (t : Icc (-ε) ε) (x : E), (t : ℝ) = 0 → H t x = x) ∧
      (∀ (t : Icc (-ε) ε) (x : E), x ∈ S → H t x = x + (t : ℝ) • f x) ∧
      (∀ (t : Icc (-ε) ε) (x : E), x ∉ U → H t x = x) ∧
      ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
        S ⊆ interior K.space ∧ ∀ t : Icc (-ε) ε,
          (∀ x, x ∉ interior K.space → H t x = x) ∧ H t '' K.space = K.space ∧
          ∃ e : K.space ≃ₜ K.space, e.IsFinitePL ∧
            ∀ x : K.space, (e x : E) = H t x := by
  obtain ⟨K, hK, hcv, hSK⟩ := hf.isCompact.exists_finite_convex_neighborhood
  obtain ⟨ε, hε, H, hc, hci, hzero, hformula, hrest⟩ :=
    hf.exists_supported_isotopy_extension K hK hcv hSK hU hSU
  exact ⟨ε, hε, H, hc, hci, hzero, hformula, fun t => (hrest t).1,
    K, hK, hcv, hSK, fun t => (hrest t).2⟩

end Geometry
