import PoincareConjecture.Definitions.M14Exponential
import Mathlib.Topology.Constructions.SumProd










set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}




theorem exists_stable_slice_neighborhood (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) {Z : G.Horizontal x} (hZ : Z ∈ H.carrier)
    {P : Set (G.Horizontal x × ℝ)} (hP : IsOpen P) (hzP : (Z, Real.sqrt τ) ∈ P) :
    ∃ U : Set G.Point, IsOpen U ∧ H.endpoint_map Z ∈ U ∧
      ∃ J : Set ℝ, IsOpen J ∧ Real.sqrt τ ∈ J ∧
        ∀ q ∈ U, G.spacetime.timeFunction q = T - τ →
          ∀ s ∈ J, ∃ W ∈ H.carrier, (W, s) ∈ P ∧ H.endpoint_map W = q := by
  obtain ⟨A, J, hA, hZA, hJ, hsJ, hAJ⟩ := mem_nhds_prod_iff'.mp (hP.mem_nhds hzP)
  obtain ⟨U0, V0, inv, hU0, _, hZU0, _, hU0carrier, _, _, hopen, _⟩ :=
    H.local_inverse Z hZ
  have himage : IsOpen (H.endpoint_slice_map '' (A ∩ U0)) :=
    hopen _ (hA.inter hU0) inter_subset_right
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp himage
  have hcenter : H.endpoint_slice_map Z ∈ H.endpoint_slice_map '' (A ∩ U0) :=
    ⟨Z, ⟨hZA, hZU0⟩, rfl⟩
  rw [← hUeq] at hcenter
  have hZU : H.endpoint_map Z ∈ U := by
    simpa only [mem_preimage, H.endpoint_slice_map_val Z hZ] using hcenter
  refine ⟨U, hU, hZU, J, hJ, hsJ, ?_⟩
  intro q hq htime s hs
  let qs : (G.slices (T - τ)).Point := ⟨q, htime⟩
  have hqs : qs ∈ H.endpoint_slice_map '' (A ∩ U0) := by
    rw [← hUeq]
    exact hq
  obtain ⟨W, hW, hWeq⟩ := hqs
  have hWcarrier := hU0carrier hW.2
  refine ⟨W, hWcarrier, hAJ ⟨hW.1, hs⟩, ?_⟩
  exact (H.endpoint_slice_map_val W hWcarrier).symm.trans
    (congrArg Subtype.val hWeq)

end PoincareConjecture.M14
