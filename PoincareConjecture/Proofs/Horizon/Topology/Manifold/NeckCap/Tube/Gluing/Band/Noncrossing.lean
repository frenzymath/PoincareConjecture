import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Partition.Sides












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}

theorem successor_upper_disjoint_compact_band (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ)
    {s : ℝ} (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hsq : s < -B.epsilon⁻¹ / 2)
    (hneg : B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier)
    (hside : ∀ x ∈ A.carrier ∩ B.carrier,
      s < (B.coordinate_inverse x).2 ↔
        f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2)
    (K S : Set M) (hK : IsCompact K)
    (hfront : frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => B.coordinate_map (q, s)))
    (havoid : Disjoint B.carrier S)
    (hupper : Disjoint (A.aboveGraph f) K) :
    Disjoint K (B.region s B.epsilon⁻¹) := by
  let X := B.region s B.epsilon⁻¹
  have hX : IsConnected X := B.isConnected_region hs.1.le le_rfl hs.2
  have hXavoid : Disjoint X
      (S ∪ range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) := by
    apply disjoint_left.mpr
    rintro x hx (hxS | ⟨q, rfl⟩)
    · exact disjoint_left.mp havoid hx.1 hxS
    · have heq := congrArg Prod.snd
        (B.coordinate_inverse_coordinate_map (z := (q, s)) ⟨mem_univ _, hs⟩)
      exact (ne_of_gt hx.2.1) heq
  have hmeet : (X ∩ Kᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := (B.isConnected_region (a := s) (b := -B.epsilon⁻¹ / 2)
      hs.1.le (by linarith [inv_pos.mpr B.epsilon_pos]) hsq).1
    have hxA := hneg ⟨hx.1, hs.1.trans hx.2.1, hx.2.2⟩
    refine ⟨x, ⟨hx.1, hx.2.1, (B.coordinate_inverse_mem x hx.1).2.2⟩, ?_⟩
    exact fun hxK => disjoint_left.mp hupper
      ⟨hxA, (hside x ⟨hxA, hx.1⟩).mp hx.2.1⟩ hxK
  have hsub : X ⊆ Kᶜ := by
    apply hX.2.subset_of_closure_inter_subset hK.isClosed.isOpen_compl hmeet
    rintro x ⟨hc, hx⟩
    by_contra hn
    have hb : x ∈ frontier Kᶜ :=
      ⟨hc, by rwa [hK.isClosed.isOpen_compl.interior_eq]⟩
    rw [frontier_compl] at hb
    exact disjoint_left.mp hXavoid hx (hfront hb)
  exact disjoint_left.mpr (fun x hxK hxX => hsub hxX hxK)

end PoincareConjecture.EpsilonNeck
