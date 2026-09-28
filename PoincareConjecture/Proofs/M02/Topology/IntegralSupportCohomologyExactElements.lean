import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCohomologyMV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSupportCohomologyUnionLeft_connecting
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q ≫
      integralSupportCohomologyConnecting K L hK hL q = 0 := by
  have h : homologyMap (biprod.inl : integralSupportCochains K ⟶
      integralSupportCochains K ⊞ integralSupportCochains L) q ≫
      homologyMap (integralSupportCochainSum K L) q =
        integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q := by
    rw [← homologyMap_comp]
    change homologyMap (biprod.inl ≫ biprod.desc _ _) q = _
    rw [biprod.inl_desc]
    rfl
  rw [← h, Category.assoc, integralSupportCohomologySum_connecting, comp_zero]

theorem integralSupportCohomologyUnionRight_connecting
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q ≫
      integralSupportCohomologyConnecting K L hK hL q = 0 := by
  have h : homologyMap (biprod.inr : integralSupportCochains L ⟶
      integralSupportCochains K ⊞ integralSupportCochains L) q ≫
      homologyMap (integralSupportCochainSum K L) q =
        integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q := by
    rw [← homologyMap_comp]
    change homologyMap (biprod.inr ≫ biprod.desc _ _) q = _
    rw [biprod.inr_desc]
    rfl
  rw [← h, Category.assoc, integralSupportCohomologySum_connecting, comp_zero]

theorem integralSupportCohomologyConnecting_interLeft
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomologyConnecting K L hK hL q ≫
      integralSupportCohomologyPushforward (inter_subset_left : K ∩ L ⊆ K) (q + 1) = 0 := by
  have h : homologyMap (integralSupportCochainDifference K L) (q + 1) ≫
      homologyMap (biprod.fst : integralSupportCochains K ⊞
        integralSupportCochains L ⟶ integralSupportCochains K) (q + 1) =
        integralSupportCohomologyPushforward (inter_subset_left : K ∩ L ⊆ K) (q + 1) := by
    rw [← homologyMap_comp]
    change homologyMap (biprod.lift _ _ ≫ biprod.fst) (q + 1) = _
    rw [biprod.lift_fst]
    rfl
  rw [← h, ← Category.assoc, integralSupportCohomologyConnecting_difference, zero_comp]

theorem integralSupportCohomologyConnecting_interRight
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomologyConnecting K L hK hL q ≫
      integralSupportCohomologyPushforward (inter_subset_right : K ∩ L ⊆ L) (q + 1) = 0 := by
  have h : homologyMap (integralSupportCochainDifference K L) (q + 1) ≫
      homologyMap (biprod.snd : integralSupportCochains K ⊞
        integralSupportCochains L ⟶ integralSupportCochains L) (q + 1) =
        -integralSupportCohomologyPushforward (inter_subset_right : K ∩ L ⊆ L) (q + 1) := by
    rw [← homologyMap_comp]
    change homologyMap (biprod.lift _ _ ≫ biprod.snd) (q + 1) = _
    rw [biprod.lift_snd, homologyMap_neg]
    rfl
  have hz : integralSupportCohomologyConnecting K L hK hL q ≫
      (-integralSupportCohomologyPushforward (inter_subset_right : K ∩ L ⊆ L) (q + 1)) = 0 := by
    rw [← h, ← Category.assoc, integralSupportCohomologyConnecting_difference, zero_comp]
  simpa only [Preadditive.comp_neg, neg_eq_zero] using hz

theorem exists_integralSupportCohomology_union_pair_of_connecting_zero
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat)
    (a : integralSupportCohomology (K ∪ L) q)
    (ha : integralSupportCohomologyConnecting K L hK hL q a = 0) :
    ∃ (aK : integralSupportCohomology K q) (bL : integralSupportCohomology L q),
      integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q aK +
        integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q bL = a := by
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (integralSupportCohomologyMayerVietoris_exact_union K L hK hL q) a ha
  let C := integralSupportCochains K
  let D := integralSupportCochains L
  change (C ⊞ D).homology q at v
  change homologyMap (integralSupportCochainSum K L) q v = a at hv
  let aK := homologyMap (biprod.fst : C ⊞ D ⟶ C) q v
  let bL := homologyMap (biprod.snd : C ⊞ D ⟶ D) q v
  have ht := congrArg (fun f => homologyMap f q)
    (biprod.total : (biprod.fst : C ⊞ D ⟶ C) ≫ biprod.inl +
      (biprod.snd : C ⊞ D ⟶ D) ≫ biprod.inr = 𝟙 _)
  simp only [homologyMap_add, homologyMap_comp, homologyMap_id] at ht
  have hd := congrArg (fun f => f v) ht
  change homologyMap (biprod.inl : C ⟶ C ⊞ D) q aK +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) q bL = v at hd
  refine ⟨aK, bL, ?_⟩
  have hl : (biprod.inl : C ⟶ C ⊞ D) ≫ integralSupportCochainSum K L =
      integralSupportCochainPushforward (subset_union_left : K ⊆ K ∪ L) := by
    change biprod.inl ≫ biprod.desc _ _ = _
    rw [biprod.inl_desc]
  have hr : (biprod.inr : D ⟶ C ⊞ D) ≫ integralSupportCochainSum K L =
      integralSupportCochainPushforward (subset_union_right : L ⊆ K ∪ L) := by
    change biprod.inr ≫ biprod.desc _ _ = _
    rw [biprod.inr_desc]
  have hl' : homologyMap (biprod.inl : C ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q =
      integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q := by
    rw [← homologyMap_comp, hl]
    rfl
  have hr' : homologyMap (biprod.inr : D ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q =
      integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q := by
    rw [← homologyMap_comp, hr]
    rfl
  have he := congrArg (homologyMap (integralSupportCochainSum K L) q) hd
  rw [map_add] at he
  change (homologyMap (biprod.inl : C ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q) aK +
    (homologyMap (biprod.inr : D ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q) bL =
    homologyMap (integralSupportCochainSum K L) q v at he
  rw [hl', hr', hv] at he
  exact he

theorem exists_integralSupportCohomology_connecting_preimage
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat)
    (c : integralSupportCohomology (K ∩ L) (q + 1))
    (hcK : integralSupportCohomologyPushforward
      (inter_subset_left : K ∩ L ⊆ K) (q + 1) c = 0)
    (hcL : integralSupportCohomologyPushforward
      (inter_subset_right : K ∩ L ⊆ L) (q + 1) c = 0) :
    ∃ a : integralSupportCohomology (K ∪ L) q,
      integralSupportCohomologyConnecting K L hK hL q a = c := by
  let C := integralSupportCochains K
  let D := integralSupportCochains L
  let v := homologyMap (integralSupportCochainDifference K L) (q + 1) c
  have hvK : homologyMap (biprod.fst : C ⊞ D ⟶ C) (q + 1) v = 0 := by
    change (homologyMap (integralSupportCochainDifference K L) (q + 1) ≫
      homologyMap (biprod.fst : C ⊞ D ⟶ C) (q + 1)) c = 0
    rw [← homologyMap_comp]
    change (homologyMap (integralSupportCochainDifference K L ≫
      (biprod.fst : C ⊞ D ⟶ C)) (q + 1)).hom c = 0
    rw [integralSupportCochainDifference, biprod.lift_fst]
    exact hcK
  have hvL : homologyMap (biprod.snd : C ⊞ D ⟶ D) (q + 1) v = 0 := by
    change (homologyMap (integralSupportCochainDifference K L) (q + 1) ≫
      homologyMap (biprod.snd : C ⊞ D ⟶ D) (q + 1)) c = 0
    rw [← homologyMap_comp]
    change (homologyMap (integralSupportCochainDifference K L ≫
      (biprod.snd : C ⊞ D ⟶ D)) (q + 1)).hom c = 0
    rw [integralSupportCochainDifference, biprod.lift_snd, homologyMap_neg]
    change -(homologyMap (integralSupportCochainPushforward inter_subset_right) (q + 1) c) = 0
    change homologyMap (integralSupportCochainPushforward inter_subset_right) (q + 1) c = 0 at hcL
    rw [hcL, neg_zero]
  have ht := congrArg (fun f => homologyMap f (q + 1))
    (biprod.total : (biprod.fst : C ⊞ D ⟶ C) ≫ biprod.inl +
      (biprod.snd : C ⊞ D ⟶ D) ≫ biprod.inr = 𝟙 _)
  simp only [homologyMap_add, homologyMap_comp, homologyMap_id] at ht
  have he := congrArg (fun f => f v) ht
  change homologyMap (biprod.inl : C ⟶ C ⊞ D) (q + 1)
      (homologyMap (biprod.fst : C ⊞ D ⟶ C) (q + 1) v) +
    homologyMap (biprod.inr : D ⟶ C ⊞ D) (q + 1)
      (homologyMap (biprod.snd : C ⊞ D ⟶ D) (q + 1) v) = v at he
  rw [hvK, hvL, map_zero, map_zero, zero_add] at he
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (integralSupportCohomologyMayerVietoris_exact_intersection K L hK hL q) c he.symm

end PoincareConjecture.Proofs.M02.Topology
