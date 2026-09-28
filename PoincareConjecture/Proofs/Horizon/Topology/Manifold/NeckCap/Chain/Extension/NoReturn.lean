import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

private theorem isPreconnected_diff_of_bridge
    {X : Type*} [TopologicalSpace X] {C S V W : Set X}
    (hC : IsPreconnected C) (hT : IsOpen (C \ S)) (hV : IsOpen V)
    (hSV : S ⊆ V) (hVW : V \ S ⊆ W) (hWT : W ⊆ C \ S)
    (hW : IsPreconnected W) : IsPreconnected (C \ S) := by
  have hforce {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
      (hdis : Disjoint A B) (hcover : C \ S ⊆ A ∪ B)
      (hAT : A ⊆ C \ S) (hBT : B ⊆ C \ S)
      (hAne : A.Nonempty) (hBne : B.Nonempty) (hWA : W ⊆ A) : False := by
    have hVB : Disjoint V B := by
      apply Set.disjoint_left.mpr
      intro x hxV hxB
      exact Set.disjoint_left.mp hdis (hWA (hVW ⟨hxV, (hBT hxB).2⟩)) hxB
    have hdis' : Disjoint (A ∪ V) B := disjoint_union_left.mpr ⟨hdis, hVB⟩
    have hcover' : C ⊆ (A ∪ V) ∪ B := by
      intro x hxC
      by_cases hxS : x ∈ S
      · exact Or.inl (Or.inr (hSV hxS))
      rcases hcover ⟨hxC, hxS⟩ with hxA | hxB
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr hxB
    rcases hC.subset_or_subset (hA.union hV) hB hdis' hcover' with hleft | hright
    · obtain ⟨x, hxB⟩ := hBne
      exact Set.disjoint_left.mp hdis' (hleft (hBT hxB).1) hxB
    · obtain ⟨x, hxA⟩ := hAne
      exact Set.disjoint_left.mp hdis hxA (hright (hAT hxA).1)
  intro A B hA hB hcover hAne hBne
  by_contra hnone
  have hAo : IsOpen ((C \ S) ∩ A) := hT.inter hA
  have hBo : IsOpen ((C \ S) ∩ B) := hT.inter hB
  have hdis : Disjoint ((C \ S) ∩ A) ((C \ S) ∩ B) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact hnone ⟨x, hxA.1, hxA.2, hxB.2⟩
  have hcover' : C \ S ⊆ ((C \ S) ∩ A) ∪ ((C \ S) ∩ B) := by
    intro x hx
    exact (hcover hx).imp (fun h => ⟨hx, h⟩) (fun h => ⟨hx, h⟩)
  rcases hW.subset_or_subset hAo hBo hdis (hWT.trans hcover') with hleft | hright
  · exact hforce hAo hBo hdis hcover' inter_subset_left inter_subset_left hAne hBne hleft
  · exact hforce hBo hAo hdis.symm
      (fun x hx => (hcover' hx).symm) inter_subset_left inter_subset_left hBne hAne hright

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem not_meets_both_halves_of_isSeparating (hN : N.IsSeparating)
    {U : Set M} (hU : IsPreconnected U)
    (hcomponent : U ⊆ connectedComponent N.center)
    (havoid : Disjoint U N.central_sphere) :
    ¬ ((U ∩ N.region (-N.epsilon⁻¹) 0).Nonempty ∧
      (U ∩ N.region 0 N.epsilon⁻¹).Nonempty) := by
  rintro ⟨hmeetneg, hmeetpos⟩
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have hneg : IsConnected (N.region (-N.epsilon⁻¹) 0) := by
    rw [← N.coordinate_negative_image]
    exact Poincare.Topology.isConnected_collar_negative (inv_pos.mpr N.epsilon_pos)
      N.coordinate
  have hpos : IsConnected (N.region 0 N.epsilon⁻¹) := by
    rw [← N.coordinate_positive_image]
    exact Poincare.Topology.isConnected_collar_positive (inv_pos.mpr N.epsilon_pos)
      N.coordinate
  let W := (U ∪ N.region (-N.epsilon⁻¹) 0) ∪ N.region 0 N.epsilon⁻¹
  have hW : IsPreconnected W := by
    apply (hU.union' hmeetneg hneg.isPreconnected).union' ?_ hpos.isPreconnected
    obtain ⟨x, hxU, hxpos⟩ := hmeetpos
    exact ⟨x, Or.inl hxU, hxpos⟩
  have hWT : W ⊆ connectedComponent N.center \ N.central_sphere := by
    intro x hx
    rcases hx with (hxU | hxneg) | hxpos
    · exact ⟨hcomponent hxU, fun hxS => Set.disjoint_left.mp havoid hxU hxS⟩
    · exact ⟨N.carrier_subset_connectedComponent hxneg.1,
        fun hxS => Set.disjoint_left.mp
          (N.central_sphere_disjoint_region (-N.epsilon⁻¹) 0 (Or.inl le_rfl)) hxS hxneg⟩
    · exact ⟨N.carrier_subset_connectedComponent hxpos.1,
        fun hxS => Set.disjoint_left.mp
          (N.central_sphere_disjoint_region 0 N.epsilon⁻¹ (Or.inr le_rfl)) hxS hxpos⟩
  have hVW : N.carrier \ N.central_sphere ⊆ W := by
    intro x hx
    rcases N.carrier_subset_region_union_central_union_region hx.1 with
      (hxneg | hxS) | hxpos
    · exact Or.inl (Or.inr hxneg)
    · exact False.elim (hx.2 hxS)
    · exact Or.inr hxpos
  apply hN.2
  refine ⟨hN.1, ?_⟩
  exact isPreconnected_diff_of_bridge isPreconnected_connectedComponent
    (isOpen_connectedComponent.sdiff N.isClosed_central_sphere) N.carrier_open
    N.central_sphere_subset hVW hWT hW

end PoincareConjecture.EpsilonNeck
