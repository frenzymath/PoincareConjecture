import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCohomologyMV








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_integralSupportCohomology_pair_lift
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat)
    (a : integralSupportCohomology K q) (b : integralSupportCohomology L q)
    (hab : integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q a +
      integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q b = 0) :
    ∃ c : integralSupportCohomology (K ∩ L) q,
      integralSupportCohomologyPushforward (inter_subset_left : K ∩ L ⊆ K) q c = a ∧
      integralSupportCohomologyPushforward (inter_subset_right : K ∩ L ⊆ L) q c = -b := by
  let C := integralSupportCochains K
  let D := integralSupportCochains L
  let v : (C ⊞ D).homology q :=
    homologyMap (biprod.inl : C ⟶ C ⊞ D) q a +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) q b
  have hfst : homologyMap (biprod.fst : C ⊞ D ⟶ C) q v = a := by
    simp [v, ← ConcreteCategory.comp_apply, ← homologyMap_comp]
  have hsnd : homologyMap (biprod.snd : C ⊞ D ⟶ D) q v = b := by
    simp [v, ← ConcreteCategory.comp_apply, ← homologyMap_comp]
  have hleft : (biprod.inl : C ⟶ C ⊞ D) ≫ integralSupportCochainSum K L =
      integralSupportCochainPushforward (subset_union_left : K ⊆ K ∪ L) := by
    change (biprod.inl : integralSupportCochains K ⟶
      integralSupportCochains K ⊞ integralSupportCochains L) ≫
        biprod.desc _ _ = _
    rw [biprod.inl_desc]
  have hright : (biprod.inr : D ⟶ C ⊞ D) ≫ integralSupportCochainSum K L =
      integralSupportCochainPushforward (subset_union_right : L ⊆ K ∪ L) := by
    change (biprod.inr : integralSupportCochains L ⟶
      integralSupportCochains K ⊞ integralSupportCochains L) ≫
        biprod.desc _ _ = _
    rw [biprod.inr_desc]
  have hleft' : homologyMap (biprod.inl : C ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q =
        integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q := by
    rw [← homologyMap_comp, hleft]
    rfl
  have hright' : homologyMap (biprod.inr : D ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q =
        integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q := by
    rw [← homologyMap_comp, hright]
    rfl
  have hv : homologyMap (integralSupportCochainSum K L) q v = 0 := by
    change homologyMap (integralSupportCochainSum K L) q
        (homologyMap (biprod.inl : C ⟶ C ⊞ D) q a +
          homologyMap (biprod.inr : D ⟶ C ⊞ D) q b) = 0
    rw [map_add]
    change (homologyMap (biprod.inl : C ⟶ C ⊞ D) q ≫
      homologyMap (integralSupportCochainSum K L) q) a +
        (homologyMap (biprod.inr : D ⟶ C ⊞ D) q ≫
          homologyMap (integralSupportCochainSum K L) q) b = 0
    rw [hleft', hright']
    exact hab
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (integralSupportCohomologyMayerVietoris_exact K L hK hL q) v hv
  change integralSupportCohomology (K ∩ L) q at c
  change homologyMap (integralSupportCochainDifference K L) q c = v at hc
  refine ⟨c, ?_, ?_⟩
  · have he := congrArg (homologyMap (biprod.fst : C ⊞ D ⟶ C) q) hc
    change homologyMap (biprod.fst : C ⊞ D ⟶ C) q
        (homologyMap (integralSupportCochainDifference K L) q c) =
      homologyMap (biprod.fst : C ⊞ D ⟶ C) q v at he
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, hfst] at he
    have hf : integralSupportCochainDifference K L ≫ (biprod.fst : C ⊞ D ⟶ C) =
        integralSupportCochainPushforward (inter_subset_left : K ∩ L ⊆ K) := by
      change biprod.lift _ _ ≫ biprod.fst = _
      rw [biprod.lift_fst]
    rw [hf] at he
    exact he
  · have he := congrArg (homologyMap (biprod.snd : C ⊞ D ⟶ D) q) hc
    change homologyMap (biprod.snd : C ⊞ D ⟶ D) q
        (homologyMap (integralSupportCochainDifference K L) q c) =
      homologyMap (biprod.snd : C ⊞ D ⟶ D) q v at he
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, hsnd] at he
    have hf : integralSupportCochainDifference K L ≫ (biprod.snd : C ⊞ D ⟶ D) =
        -integralSupportCochainPushforward (inter_subset_right : K ∩ L ⊆ L) := by
      change biprod.lift _ _ ≫ biprod.snd = _
      rw [biprod.lift_snd]
    rw [hf] at he
    have hneg : homologyMap (integralSupportCochainPushforward
        (inter_subset_right : K ∩ L ⊆ L)) q c = -b := by
      have he' : -homologyMap (integralSupportCochainPushforward
          (inter_subset_right : K ∩ L ⊆ L)) q c = b := by
        simpa only [homologyMap_neg, ModuleCat.hom_neg, LinearMap.neg_apply] using he
      simpa only [neg_neg] using congrArg Neg.neg he'
    change homologyMap (integralSupportCochainPushforward
      (inter_subset_right : K ∩ L ⊆ L)) q c = -b
    exact hneg

end PoincareConjecture.Proofs.M02.Topology
