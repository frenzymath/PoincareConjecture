import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Proofs.M25.Mathlib.OppositeCollarComponents

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem exists_opposite_central_components (N : EpsilonNeck g)
    (hsep : N.IsSeparating) :
    ∃ a b : M,
      a ∈ N.region (-N.epsilon⁻¹) 0 ∧
      b ∈ N.region 0 N.epsilon⁻¹ ∧
      let A := connectedComponentIn N.central_sphereᶜ a
      let B := connectedComponentIn N.central_sphereᶜ b
      N.region (-N.epsilon⁻¹) 0 ⊆ A ∧
      N.region 0 N.epsilon⁻¹ ⊆ B ∧
      A ≠ B ∧
      frontier A = N.central_sphere ∧
      frontier B = N.central_sphere ∧
      A ∪ N.central_sphere ∪ B = connectedComponent N.center := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hcentral : range (fun q : UnitTwoSphere =>
      (N.coordinate (q, ⟨0, neg_lt_zero.mpr hL, hL⟩) : M)) =
      N.central_sphere := by
    apply Subset.antisymm
    · rintro x ⟨q, rfl⟩
      apply (N.mem_central_sphere_iff _).mpr
      refine ⟨(N.coordinate _).property, ?_⟩
      rw [N.coordinate_inverse_left]
    · intro x hx
      obtain ⟨hxc, hx0⟩ := (N.mem_central_sphere_iff x).mp hx
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      have he := congrArg Subtype.val (N.coordinate_inverse_right x hxc)
      simpa only [hx0] using he
  have hnegative : (fun z => (N.coordinate z : M)) ''
      {z | (z.2 : ℝ) < 0} = N.region (-N.epsilon⁻¹) 0 := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨(N.coordinate z).property, ?_, ?_⟩
      · simpa only [N.coordinate_inverse_left] using z.2.property.1
      · simpa only [N.coordinate_inverse_left, mem_ofPred_eq] using hz
    · intro x hx
      refine ⟨((N.coordinate_inverse x).1,
        ⟨(N.coordinate_inverse x).2, (N.coordinate_inverse_mem x hx.1).2⟩),
        hx.2.2, ?_⟩
      exact congrArg Subtype.val (N.coordinate_inverse_right x hx.1)
  have hpositive : (fun z => (N.coordinate z : M)) ''
      {z | 0 < (z.2 : ℝ)} = N.region 0 N.epsilon⁻¹ := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨(N.coordinate z).property, ?_, ?_⟩
      · simpa only [N.coordinate_inverse_left, mem_ofPred_eq] using hz
      · simpa only [N.coordinate_inverse_left] using z.2.property.2
    · intro x hx
      refine ⟨((N.coordinate_inverse x).1,
        ⟨(N.coordinate_inverse x).2, (N.coordinate_inverse_mem x hx.1).2⟩),
        hx.2.1, ?_⟩
      exact congrArg Subtype.val (N.coordinate_inverse_right x hx.1)
  have hnegconn : IsConnected (N.region (-N.epsilon⁻¹) 0) := by
    rw [← hnegative]
    exact Poincare.Topology.isConnected_collar_negative hL N.coordinate
  have hposconn : IsConnected (N.region 0 N.epsilon⁻¹) := by
    rw [← hpositive]
    exact Poincare.Topology.isConnected_collar_positive hL N.coordinate
  obtain ⟨a, ha⟩ := hnegconn.nonempty
  obtain ⟨b, hb⟩ := hposconn.nonempty
  have hnegS : N.region (-N.epsilon⁻¹) 0 ⊆ N.central_sphereᶜ := by
    intro x hx hxS
    exact Set.disjoint_left.mp
      (N.central_sphere_disjoint_region _ _ (Or.inl le_rfl)) hxS hx
  have hposS : N.region 0 N.epsilon⁻¹ ⊆ N.central_sphereᶜ := by
    intro x hx hxS
    exact Set.disjoint_left.mp
      (N.central_sphere_disjoint_region _ _ (Or.inr le_rfl)) hxS hx
  let A := connectedComponentIn N.central_sphereᶜ a
  let B := connectedComponentIn N.central_sphereᶜ b
  have hA : IsOpen A := N.isClosed_central_sphere.isOpen_compl.connectedComponentIn
  have hAc : IsConnected A := isConnected_connectedComponentIn_iff.mpr (hnegS ha)
  have hAS : A ⊆ N.central_sphereᶜ := connectedComponentIn_subset _ _
  have hBS : B ⊆ N.central_sphereᶜ := connectedComponentIn_subset _ _
  have hnegA : N.region (-N.epsilon⁻¹) 0 ⊆ A :=
    hnegconn.isPreconnected.subset_connectedComponentIn ha hnegS
  have hposB : N.region 0 N.epsilon⁻¹ ⊆ B :=
    hposconn.isPreconnected.subset_connectedComponentIn hb hposS
  have hfront : N.central_sphere ⊆ frontier A ∩ frontier B := by
    intro x hx
    obtain ⟨q, rfl⟩ := hcentral.symm ▸ hx
    have hn := Poincare.Topology.collar_center_mem_closure_negative hL N.coordinate q
    have hp := Poincare.Topology.collar_center_mem_closure_positive hL N.coordinate q
    rw [hnegative] at hn
    rw [hpositive] at hp
    refine ⟨⟨closure_mono hnegA hn, ?_⟩, ⟨closure_mono hposB hp, ?_⟩⟩
    · intro hi
      exact hAS (interior_subset hi) (hcentral ▸ mem_range_self q)
    · intro hi
      exact hBS (interior_subset hi) (hcentral ▸ mem_range_self q)
  have hne : A ≠ B := by
    intro heq
    have hclosure : closure A = A ∪ N.central_sphere := by
      apply Subset.antisymm
        (Poincare.Topology.closure_connectedComponentIn_compl_subset
          N.isClosed_central_sphere a)
      exact union_subset subset_closure (fun _ hx => (hfront hx).1.1)
    have hcarrier : N.carrier ⊆ A ∪ N.central_sphere := by
      intro x hx
      rcases N.carrier_subset_region_union_central_union_region hx with (hn | hs) | hp
      · exact Or.inl (hnegA hn)
      · exact Or.inr hs
      · exact Or.inl (heq.symm ▸ hposB hp)
    have hopenEq : A ∪ N.central_sphere = A ∪ N.carrier :=
      Subset.antisymm (union_subset_union_right A N.central_sphere_subset)
        (union_subset (fun _ hx => Or.inl hx) hcarrier)
    have hclopen : IsClopen (A ∪ N.central_sphere) :=
      ⟨hclosure ▸ isClosed_closure, hopenEq.symm ▸ hA.union N.carrier_open⟩
    have hconn : IsConnected (A ∪ N.central_sphere) := hclosure ▸ hAc.closure
    have hcenter : N.center ∈ A ∪ N.central_sphere := Or.inr N.center_on_central_sphere
    have hK : A ∪ N.central_sphere = connectedComponent N.center :=
      Subset.antisymm (hconn.subset_connectedComponent hcenter)
        (hclopen.connectedComponent_subset hcenter)
    have hdiff : connectedComponent N.center \ N.central_sphere = A := by
      rw [← hK]
      ext x
      constructor
      · rintro ⟨hxA | hxS, hxout⟩
        · exact hxA
        · exact False.elim (hxout hxS)
      · intro hx
        exact ⟨Or.inl hx, hAS hx⟩
    exact hsep.2 (hdiff.symm ▸ hAc)
  have hopp := Poincare.Topology.opposite_collar_components hL N.carrier_open
    N.coordinate (a := a) (b := b)
  dsimp only at hopp
  rw [hcentral] at hopp
  have hout := hopp (hnegS ha) (hposS hb) hne hfront
  refine ⟨a, b, ha, hb, hnegA, hposB, hne, hout.1, hout.2.1, ?_⟩
  have hcomp := connectedComponent_eq
    (N.m25_carrier_subset_connectedComponent ha.1)
  exact hout.2.2.2.2.trans hcomp.symm

end PoincareConjecture.EpsilonNeck
