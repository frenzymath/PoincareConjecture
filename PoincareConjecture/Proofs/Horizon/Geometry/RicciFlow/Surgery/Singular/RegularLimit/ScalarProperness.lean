import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.ScalarEscape

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem scalar_limit_proper_and_bounded_below (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    {X : Type v} [TopologicalSpace X] (i : X → M) (hi : Topology.IsEmbedding i)
    (hrange : range i = H.reference.regularLimitSet)
    (S : X → ℝ) (hS : Continuous S)
    (hlim : ∀ x : X, Tendsto (fun t => H.reference.scalar t (i x))
      (𝓝[<] T) (𝓝 (S x))) :
    (∃ L : ℝ, ∀ x : X, L ≤ S x) ∧
      ∀ K : Set ℝ, IsCompact K → IsCompact (S ⁻¹' K) := by
  have hwindow : ∀ᶠ t in 𝓝[<] T, t ∈ Ico H.reference.tMinus T := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds H.reference.tMinus_lt).filter_mono nhdsWithin_le_nhds] with t ht hgt
    exact ⟨hgt.le, ht⟩
  constructor
  · obtain ⟨L, hL⟩ := H.reference_scalar_lower_bound
    exact ⟨L, fun x => ge_of_tendsto (hlim x) (hwindow.mono fun t ht => hL t ht (i x))⟩
  · intro K hK
    obtain ⟨B, hB⟩ := hK.bddAbove
    obtain ⟨A, hA, hAreg, hconfine⟩ := H.exists_compact_containing_liminf_sublevel P04 (B + 1)
    have hArange : A ⊆ range i := by rwa [hrange]
    have hcompact : IsCompact (i ⁻¹' A) := hi.isInducing.isCompact_preimage' hA hArange
    apply hcompact.of_isClosed_subset (hK.isClosed.preimage hS)
    intro x hx
    apply hconfine (i x)
    intro a ha
    have hnear : ∀ᶠ t in 𝓝[<] T, a < t :=
      (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds
    have hscalar : ∀ᶠ t in 𝓝[<] T, H.reference.scalar t (i x) < B + 1 :=
      (hlim x).eventually (eventually_lt_nhds (by linarith [hB hx] : S x < B + 1))
    obtain ⟨t, ht, hta, htB⟩ := (hwindow.and (hnear.and hscalar)).exists
    exact ⟨t, hta, ht, htB.le⟩

end PoincareConjecture.SingularTimeAssumptions
