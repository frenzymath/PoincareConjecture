import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.NonFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.DeepHorn

private theorem frontier_component_compl_subset
    {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    {S : Set M} (hS : IsClosed S) {p : M} (hp : p ∈ Sᶜ) :
    frontier (connectedComponentIn Sᶜ p) ⊆ S := by
  intro x hx
  by_contra hxS
  have hmem : (⟨x, hxS⟩ : ↥(Sᶜ)) ∈ connectedComponent (⟨p, hp⟩ : ↥(Sᶜ)) := by
    rw [← (isClosed_connectedComponent (x := (⟨p, hp⟩ : ↥(Sᶜ)))).closure_eq]
    apply closure_subtype.mpr
    rw [← connectedComponentIn_eq_image hp]
    exact hx.1
  have hxC : x ∈ connectedComponentIn Sᶜ p := by
    rw [connectedComponentIn_eq_image hp]
    exact ⟨⟨x, hxS⟩, hmem, rfl⟩
  exact hx.2 ((hS.isOpen_compl.connectedComponentIn).interior_eq.symm ▸ hxC)

end PoincareConjecture.DeepHorn

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem complementary_component_frontiers (N : EpsilonNeck g) (hN : N.IsSeparating)
    {p q : M} (hp : p ∈ N.region (-N.epsilon⁻¹) 0)
    (hq : q ∈ N.region 0 N.epsilon⁻¹) :
    let A := connectedComponentIn N.central_sphereᶜ p
    let B := connectedComponentIn N.central_sphereᶜ q
    IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B ∧
      frontier (closure A) = N.central_sphere ∧ frontier (closure B) = N.central_sphere ∧
      (interior (closure A)).Nonempty ∧ (interior (closure B)).Nonempty := by
  dsimp only
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let A := connectedComponentIn N.central_sphereᶜ p
  let B := connectedComponentIn N.central_sphereᶜ q
  have hnegavoid : N.region (-N.epsilon⁻¹) 0 ⊆ N.central_sphereᶜ := by
    intro x hx hxS
    exact disjoint_left.mp (N.central_sphere_disjoint_region _ _ (Or.inl le_rfl)) hxS hx
  have hposavoid : N.region 0 N.epsilon⁻¹ ⊆ N.central_sphereᶜ := by
    intro x hx hxS
    exact disjoint_left.mp (N.central_sphere_disjoint_region _ _ (Or.inr le_rfl)) hxS hx
  have hi := inv_pos.mpr N.epsilon_pos
  have hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A :=
    (N.isConnected_region le_rfl hi.le (neg_lt_zero.mpr hi)).isPreconnected.subset_connectedComponentIn
      hp hnegavoid
  have hpos : N.region 0 N.epsilon⁻¹ ⊆ B :=
    (N.isConnected_region (neg_nonpos.mpr hi.le) le_rfl hi).isPreconnected.subset_connectedComponentIn
      hq hposavoid
  have hpA : p ∈ A := mem_connectedComponentIn (hnegavoid hp)
  have hqB : q ∈ B := mem_connectedComponentIn (hposavoid hq)
  have hAo : IsOpen A := N.isClosed_central_sphere.isOpen_compl.connectedComponentIn
  have hBo : IsOpen B := N.isClosed_central_sphere.isOpen_compl.connectedComponentIn
  have hAc : IsConnected A := isConnected_connectedComponentIn_iff.mpr (hnegavoid hp)
  have hBc : IsConnected B := isConnected_connectedComponentIn_iff.mpr (hposavoid hq)
  have hAC : A ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hp.1)]
    exact hAc.isPreconnected.subset_connectedComponent hpA
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    have heq : A = B := (connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm
    apply N.not_meets_both_halves_of_isSeparating hN hAc.isPreconnected hAC
      (disjoint_left.mpr fun y hy => connectedComponentIn_subset _ _ hy)
    exact ⟨⟨p, hpA, hp⟩, ⟨q, heq.symm ▸ hqB, hq⟩⟩
  have hSneg : N.central_sphere ⊆ closure (N.region (-N.epsilon⁻¹) 0) := by
    rw [← N.coordinate_central_range, ← N.coordinate_negative_image]
    rintro x ⟨y, rfl⟩
    exact Poincare.Topology.collar_center_mem_closure_negative hi N.coordinate y
  have hSpos : N.central_sphere ⊆ closure (N.region 0 N.epsilon⁻¹) := by
    rw [← N.coordinate_central_range, ← N.coordinate_positive_image]
    rintro x ⟨y, rfl⟩
    exact Poincare.Topology.collar_center_mem_closure_positive hi N.coordinate y
  have hSA : N.central_sphere ⊆ closure A := hSneg.trans (closure_mono hneg)
  have hSB : N.central_sphere ⊆ closure B := hSpos.trans (closure_mono hpos)
  have hfront {C D : Set M} {r : M} (hC : C = connectedComponentIn N.central_sphereᶜ r)
      (hr : r ∈ N.central_sphereᶜ) (hDo : IsOpen D) (hCD : Disjoint C D)
      (hSC : N.central_sphere ⊆ closure C) (hSD : N.central_sphere ⊆ closure D) :
      frontier (closure C) = N.central_sphere := by
    apply Subset.antisymm
    · apply frontier_closure_subset.trans
      rw [hC]
      exact DeepHorn.frontier_component_compl_subset N.isClosed_central_sphere hr
    · intro x hx
      rw [frontier_eq_closure_inter_closure, closure_closure]
      refine ⟨hSC hx, closure_mono ?_ (hSD hx)⟩
      exact (hCD.closure_left hDo).symm.subset_compl_right
  refine ⟨hAo, hBo, hAc, hBc, hAB, hneg, hpos,
    hfront rfl (hnegavoid hp) hBo hAB hSA hSB,
    hfront rfl (hposavoid hq) hAo hAB.symm hSB hSA, ?_, ?_⟩
  · exact ⟨p, hAo.subset_interior_iff.mpr subset_closure hpA⟩
  · exact ⟨q, hBo.subset_interior_iff.mpr subset_closure hqB⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.StrongHorn



theorem exists_complementary_components_escape_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T ε : ℝ}
        (E : GeneralizedFlowExtension F T),
        ∀ (A : RepairedNeckCapTopologyTheory.{u}), 0 < ε → ε ≤ ε₀ → ε ≤ A.epsilon₀ →
        ∀ (horn : StrongHorn E ε) (N : TerminalStrongNeck E ε), N.center ∈ horn.carrier →
        ∃ hhalf : ε < 1 / 2,
          ∀ p ∈ (N.spatialNeck hhalf).region (-ε⁻¹) 0,
          ∀ q ∈ (N.spatialNeck hhalf).region 0 ε⁻¹,
          ∀ K : Set (E.extended.slice T).carrier, IsCompact K → K ⊆ horn.carrier →
            ¬ connectedComponentIn N.central_sphereᶜ p ⊆ K ∧
              ¬ connectedComponentIn N.central_sphereᶜ q ⊆ K := by
  obtain ⟨ε₁, hε₁, hsmall, hno⟩ := exists_no_compact_filling_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hsep⟩ := exists_boundary_sphere_transport.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro F T ε E A hεpos hε hA horn N hN
  have hhalf : ε < 1 / 2 :=
    (hε.trans ((min_le_left _ _).trans hsmall)).trans_lt (by norm_num)
  obtain ⟨_, _, _, _, _, hseparating⟩ :=
    hsep E hεpos (hε.trans (min_le_right _ _)) horn (N.spatialNeck hhalf) rfl hN
  refine ⟨hhalf, ?_⟩
  intro p hp q hq K hK hKH
  obtain ⟨_, _, _, _, _, _, _, hfp, hfq, hip, hiq⟩ :=
    (N.spatialNeck hhalf).complementary_component_frontiers hseparating hp hq
  have hescape (r : (E.extended.slice T).carrier)
      (hfront : frontier (closure (connectedComponentIn N.central_sphereᶜ r)) = N.central_sphere)
      (hint : (interior (closure (connectedComponentIn N.central_sphereᶜ r))).Nonempty) :
      ¬ connectedComponentIn N.central_sphereᶜ r ⊆ K := by
    intro hsub
    have hcl : closure (connectedComponentIn N.central_sphereᶜ r) ⊆ K :=
      closure_minimal hsub hK.isClosed
    exact hno E A hεpos (hε.trans (min_le_left _ _)) hA horn N hN _
      (hcl.trans hKH) hfront hint (hK.of_isClosed_subset isClosed_closure hcl)
  exact ⟨hescape p hfp hip, hescape q hfq hiq⟩

end PoincareConjecture.StrongHorn
