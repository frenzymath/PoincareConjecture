import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem positive_image_eq_diff_nonpositive_image {U : Opens M}
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞) :
    (fun p : RoundCylinderSpace => (F p : M)) '' {p | 0 < p.2} =
      (U : Set M) \ (fun p : RoundCylinderSpace => (F p : M)) '' {p | p.2 ≤ 0} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    change 0 < p.2 at hp
    refine ⟨(F p).property, ?_⟩
    rintro ⟨q, hq, heq⟩
    have hqp : q = p := F.injective (Subtype.ext heq)
    subst q
    change p.2 ≤ 0 at hq
    exact not_lt_of_ge hq hp
  · rintro ⟨hxU, hx⟩
    let p := F.symm ⟨x, hxU⟩
    have hpval : (F p : M) = x :=
      congrArg (fun y : U => (y : M)) (F.apply_symm_apply ⟨x, hxU⟩)
    refine ⟨p, ?_, hpval⟩
    change 0 < p.2
    by_contra hp
    exact hx ⟨p, le_of_not_gt hp, hpval⟩

theorem isConnected_positive_image {U : Opens M}
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞) :
    IsConnected ((fun p : RoundCylinderSpace => (F p : M)) '' {p | 0 < p.2}) := by
  have hsource : IsConnected ({p : RoundCylinderSpace | 0 < p.2}) := by
    have h := (isConnected_univ (α := UnitTwoSphere)).prod
      (isConnected_Ioi : IsConnected (Ioi (0 : ℝ)))
    convert h using 1
    ext p
    simp
  exact hsource.image _ (continuous_subtype_val.comp F.continuous).continuousOn

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem two_sided_partition (N : EpsilonNeck g) (hN : N.IsSeparating)
    (U V : Opens M) (hNU : N.carrier ⊆ U) (hNV : N.carrier ⊆ V)
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
    (B : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace V ∞)
    (hF : (fun p : RoundCylinderSpace => (F p : M)) '' {p | p.2 ≤ 0} =
      {x | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ 0})
    (hB : (fun p : RoundCylinderSpace => (B p : M)) '' {p | p.2 ≤ 0} =
      {x | x ∈ N.carrier ∧ 0 ≤ (N.coordinate_inverse x).2}) :
    let R := (fun p : RoundCylinderSpace => (F p : M)) '' {p | 0 < p.2}
    let L := (fun p : RoundCylinderSpace => (B p : M)) '' {p | 0 < p.2}
    Disjoint R L ∧ Disjoint R N.central_sphere ∧ Disjoint L N.central_sphere ∧
      (U : Set M) ∪ V = (R ∪ N.central_sphere) ∪ L ∧
      (U : Set M) ∩ V = N.carrier := by
  dsimp only
  let R := (fun p : RoundCylinderSpace => (F p : M)) '' {p | 0 < p.2}
  let L := (fun p : RoundCylinderSpace => (B p : M)) '' {p | 0 < p.2}
  change Disjoint R L ∧ Disjoint R N.central_sphere ∧ Disjoint L N.central_sphere ∧
    (U : Set M) ∪ V = (R ∪ N.central_sphere) ∪ L ∧ (U : Set M) ∩ V = N.carrier
  have hR : R = (U : Set M) \ {x | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ 0} := by
    dsimp only [R]
    rw [positive_image_eq_diff_nonpositive_image, hF]
  have hL : L = (V : Set M) \ {x | x ∈ N.carrier ∧ 0 ≤ (N.coordinate_inverse x).2} := by
    dsimp only [L]
    rw [positive_image_eq_diff_nonpositive_image, hB]
  have hpositive : N.region 0 N.epsilon⁻¹ ⊆ R := by
    intro x hx
    rw [hR]
    exact ⟨hNU hx.1, fun h => not_le_of_gt hx.2.1 h.2⟩
  have hnegative : N.region (-N.epsilon⁻¹) 0 ⊆ L := by
    intro x hx
    rw [hL]
    exact ⟨hNV hx.1, fun h => not_le_of_gt hx.2.2 h.2⟩
  have hRavoid : Disjoint R N.central_sphere := by
    apply disjoint_left.mpr
    intro x hx hxS
    have hs := (N.mem_central_sphere_iff x).mp hxS
    rw [hR] at hx
    exact hx.2 ⟨hs.1, hs.2.le⟩
  have hLavoid : Disjoint L N.central_sphere := by
    apply disjoint_left.mpr
    intro x hx hxS
    have hs := (N.mem_central_sphere_iff x).mp hxS
    rw [hL] at hx
    exact hx.2 ⟨hs.1, hs.2.ge⟩
  have hdisjoint : Disjoint R L := by
    apply disjoint_left.mpr
    intro x hxR hxL
    have hconn := (isConnected_positive_image F).isPreconnected.union
      x hxR hxL (isConnected_positive_image B).isPreconnected
    have hi := inv_pos.mpr N.epsilon_pos
    obtain ⟨p, hp⟩ := (N.isConnected_region (a := 0) (b := N.epsilon⁻¹)
      (by linarith) le_rfl hi).nonempty
    obtain ⟨q, hq⟩ := (N.isConnected_region (a := -N.epsilon⁻¹) (b := 0)
      le_rfl hi.le (by linarith)).nonempty
    have hcomponent : R ∪ L ⊆ connectedComponent N.center := by
      rw [connectedComponent_eq (N.carrier_subset_connectedComponent hp.1)]
      exact hconn.subset_connectedComponent (Or.inl (hpositive hp))
    apply N.not_meets_both_halves_of_isSeparating hN hconn hcomponent
      (disjoint_union_left.mpr ⟨hRavoid, hLavoid⟩)
    exact ⟨⟨q, Or.inr (hnegative hq), hq⟩, ⟨p, Or.inl (hpositive hp), hp⟩⟩
  refine ⟨hdisjoint, hRavoid, hLavoid, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      by_cases hxN : x ∈ N.carrier
      · rcases lt_trichotomy (N.coordinate_inverse x).2 0 with hn | hz | hp
        · exact Or.inr (hnegative ⟨hxN, (N.coordinate_inverse_mem x hxN).2.1, hn⟩)
        · exact Or.inl (Or.inr ((N.mem_central_sphere_iff x).mpr ⟨hxN, hz⟩))
        · exact Or.inl (Or.inl (hpositive ⟨hxN, hp, (N.coordinate_inverse_mem x hxN).2.2⟩))
      · rcases hx with hx | hx
        · exact Or.inl (Or.inl (by rw [hR]; exact ⟨hx, fun h => hxN h.1⟩))
        · exact Or.inr (by rw [hL]; exact ⟨hx, fun h => hxN h.1⟩)
    · intro x hx
      rcases hx with (hxR | hxS) | hxL
      · exact Or.inl ((hR ▸ hxR).1)
      · exact Or.inl (hNU (N.central_sphere_subset hxS))
      · exact Or.inr ((hL ▸ hxL).1)
  · apply Subset.antisymm
    · intro x hx
      by_contra hxN
      have hxR : x ∈ R := by rw [hR]; exact ⟨hx.1, fun h => hxN h.1⟩
      have hxL : x ∈ L := by rw [hL]; exact ⟨hx.2, fun h => hxN h.1⟩
      exact disjoint_left.mp hdisjoint hxR hxL
    · exact fun _ hx => ⟨hNU hx, hNV hx⟩

end PoincareConjecture.CylinderGluing

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}



theorem two_sided_halfchain_partition
    (C : BalancedNeckChain g ε) (hbi : C.shape = .biInfinite) (a : ℤ)
    (hsep : (C.neck a).IsSeparating)
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (C.forwardHalf hbi a).unionOpen ∞)
    (B : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (C.backwardHalf hbi a).unionOpen ∞)
    (hF : (fun p : RoundCylinderSpace => (F p : M)) '' {p | p.2 ≤ 0} =
      {x | x ∈ (C.neck a).carrier ∧ ((C.neck a).coordinate_inverse x).2 ≤ 0})
    (hB : (fun p : RoundCylinderSpace => (B p : M)) '' {p | p.2 ≤ 0} =
      {x | x ∈ (C.neck a).carrier ∧ 0 ≤ ((C.neck a).coordinate_inverse x).2}) :
    let R := (fun p : RoundCylinderSpace => (F p : M)) '' {p | 0 < p.2}
    let L := (fun p : RoundCylinderSpace => (B p : M)) '' {p | 0 < p.2}
    Disjoint R L ∧ Disjoint R (C.neck a).central_sphere ∧
      Disjoint L (C.neck a).central_sphere ∧
      (C.unionOpen : Set M) = (R ∪ (C.neck a).central_sphere) ∪ L ∧
      ((C.forwardHalf hbi a).unionOpen : Set M) ∩ (C.backwardHalf hbi a).unionOpen =
        (C.neck a).carrier := by
  have h := CylinderGluing.two_sided_partition (C.neck a) hsep
    (C.forwardHalf hbi a).unionOpen (C.backwardHalf hbi a).unionOpen
    (C.neck_subset_forwardHalf_union hbi a) (C.neck_subset_backwardHalf_union hbi a) F B hF hB
  dsimp only at h ⊢
  rwa [C.union_forwardHalf_backwardHalf hbi a] at h

end PoincareConjecture.BalancedNeckChain
