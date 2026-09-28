import PoincareConjecture.Proofs.M38.CirclePullback
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38.CirclePullback



theorem projection_injOn_precompact_component
    {M : Type*} [TopologicalSpace M] (π : M → UnitCircle) (hπ : Continuous π)
    (U : Set M) (a : CirclePullback π)
    (hcompact : IsCompact (closure (connectedComponentIn (projection π ⁻¹' U) a))) :
    InjOn (projection π) (connectedComponentIn (projection π ⁻¹' U) a) := by
  let V := projection π ⁻¹' U
  let C := connectedComponentIn V a
  have hstable (n : ℤ) (z : CirclePullback π) (hz : z ∈ C) (hnz : n +ᵥ z ∈ C) :
      (fun x : CirclePullback π => n +ᵥ x) '' C ⊆ C := by
    have hsub : (fun x : CirclePullback π => n +ᵥ x) '' C ⊆ V := by
      rintro _ ⟨x, hx, rfl⟩
      change projection π (n +ᵥ x) ∈ U
      rw [projection_vadd]
      exact connectedComponentIn_subset V a hx
    have hc : IsPreconnected ((fun x : CirclePullback π => n +ᵥ x) '' C) :=
      isPreconnected_connectedComponentIn.image _ (continuous_const_vadd n).continuousOn
    have hs := hc.subset_connectedComponentIn (mem_image_of_mem _ hz) hsub
    exact hs.trans_eq (connectedComponentIn_eq hnz).symm
  intro y hy z hz heq
  obtain ⟨n, hn⟩ := (projection_isAddQuotientCoveringMap π hπ).apply_eq_iff_mem_orbit.mp heq
  change n +ᵥ z = y at hn
  have hnonpos (k : ℤ) (hstable : (fun x : CirclePullback π => k +ᵥ x) '' C ⊆ C) :
      (k : ℝ) ≤ 0 := by
    have hclosure : (fun x : CirclePullback π => k +ᵥ x) '' closure C ⊆ closure C :=
      (image_closure_subset_closure_image (continuous_const_vadd k)).trans (closure_mono hstable)
    obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn ⟨y, subset_closure hy⟩
      (continuous_height π).continuousOn
    have hle := hmax (hclosure (mem_image_of_mem _ hp))
    change height π p + k ≤ height π p at hle
    linarith
  have hle := hnonpos n (hstable n z hz (hn.symm ▸ hy))
  have hneg : -n +ᵥ y = z := by rw [← hn, neg_vadd_vadd]
  have hge := hnonpos (-n) (hstable (-n) y hy (hneg.symm ▸ hz))
  have hnreal : (n : ℝ) = 0 := by
    rw [Int.cast_neg] at hge
    linarith
  have hnzero : n = 0 := by exact_mod_cast hnreal
  simpa only [hnzero, zero_vadd] using hn.symm

end PoincareConjecture.M38.CirclePullback
