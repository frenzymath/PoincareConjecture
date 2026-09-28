import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralMayerVietorisExcision

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

abbrev integralSupportChains (K : Set X) := integralRelativeChains Kᶜ

abbrev integralSupportHomology (K : Set X) (n : Nat) :=
  integralRelativeHomology Kᶜ n

def integralSupportRestriction {K L : Set X} (h : K ⊆ L) :
    integralSupportChains L ⟶ integralSupportChains K :=
  integralRelativeRestriction (Set.compl_subset_compl.mpr h)

@[reassoc (attr := simp)]
theorem integralSupportRestriction_projection {K L : Set X} (h : K ⊆ L) :
    integralRelativeProjection Lᶜ ≫ integralSupportRestriction h =
      integralRelativeProjection Kᶜ :=
  integralRelativeRestriction_projection _

@[reassoc (attr := simp)]
theorem integralSupportRestriction_comp {K L D : Set X}
    (hKL : K ⊆ L) (hLD : L ⊆ D) :
    integralSupportRestriction hLD ≫ integralSupportRestriction hKL =
      integralSupportRestriction (hKL.trans hLD) := by
  apply (cancel_epi (integralRelativeProjection Dᶜ)).mp
  simp only [← Category.assoc, integralSupportRestriction_projection]

def integralSupportHomologyRestriction {K L : Set X} (h : K ⊆ L) (n : Nat) :
    integralSupportHomology L n ⟶ integralSupportHomology K n :=
  homologyMap (integralSupportRestriction h) n

@[reassoc (attr := simp)]
theorem integralSupportHomologyRestriction_comp {K L D : Set X}
    (hKL : K ⊆ L) (hLD : L ⊆ D) (n : Nat) :
    integralSupportHomologyRestriction hLD n ≫ integralSupportHomologyRestriction hKL n =
      integralSupportHomologyRestriction (hKL.trans hLD) n := by
  rw [integralSupportHomologyRestriction, integralSupportHomologyRestriction,
    ← homologyMap_comp, integralSupportRestriction_comp]
  rfl

def integralRelativeSetIso {A B : Set X} (h : A = B) :
    integralRelativeChains A ≅ integralRelativeChains B :=
  eqToIso (congrArg integralRelativeChains h)

@[reassoc (attr := simp)]
theorem integralRelativeSetIso_projection {A B : Set X} (h : A = B) :
    integralRelativeProjection A ≫ (integralRelativeSetIso h).hom =
      integralRelativeProjection B := by
  subst B
  simp [integralRelativeSetIso]

def integralSupportUnionMap (K L : Set X) :
    integralSupportChains (K ∪ L) ⟶ integralSupportChains K ⊞ integralSupportChains L :=
  biprod.lift (integralSupportRestriction (Set.subset_union_left : K ⊆ K ∪ L))
    (integralSupportRestriction (Set.subset_union_right : L ⊆ K ∪ L))

def integralSupportDifference (K L : Set X) :
    integralSupportChains K ⊞ integralSupportChains L ⟶
      integralSupportChains (K ∩ L) :=
  biprod.desc (integralSupportRestriction (Set.inter_subset_left : K ∩ L ⊆ K))
    (-integralSupportRestriction (Set.inter_subset_right : K ∩ L ⊆ L))

def integralSupportComparison (K L : Set X) :
    integralSumQuotient Kᶜ Lᶜ ⟶ integralSupportChains (K ∩ L) :=
  integralSumComparison Kᶜ Lᶜ ≫ (integralRelativeSetIso (Set.compl_inter K L).symm).hom

@[reassoc (attr := simp)]
theorem integralSupportComparison_left (K L : Set X) :
    integralSumProjection Kᶜ Lᶜ ≫ integralSupportComparison K L =
      integralSupportRestriction (Set.inter_subset_left : K ∩ L ⊆ K) := by
  apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
  simp only [integralSupportComparison, ← Category.assoc,
    integralSumProjection_comparison, integralRelativeRestriction_projection,
    integralRelativeSetIso_projection, integralSupportRestriction_projection]

@[reassoc (attr := simp)]
theorem integralSupportComparison_right (K L : Set X) :
    integralSumRightProjection Kᶜ Lᶜ ≫ integralSupportComparison K L =
      integralSupportRestriction (Set.inter_subset_right : K ∩ L ⊆ L) := by
  apply (cancel_epi (integralRelativeProjection Lᶜ)).mp
  rw [← Category.assoc, integralProjection_sumRightProjection,
    integralSumAmbientProjection, Category.assoc, integralSupportComparison_left,
    integralSupportRestriction_projection, integralSupportRestriction_projection]

@[reassoc (attr := simp)]
theorem integralSupportComparison_difference (K L : Set X) :
    integralSumDifference Kᶜ Lᶜ ≫ integralSupportComparison K L =
      integralSupportDifference K L := by
  apply biprod.hom_ext'
  · simp [integralSumDifference, integralSupportDifference]
  · simp [integralSumDifference, integralSupportDifference, Preadditive.neg_comp]

def integralSupportIntermediateSequence (K L : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralSupportUnionMap K L) (integralSumDifference Kᶜ Lᶜ) (by
    rw [integralSupportUnionMap, integralSumDifference, biprod.lift_desc,
      Preadditive.comp_neg, ← sub_eq_add_neg]
    apply sub_eq_zero.mpr
    apply (cancel_epi (integralRelativeProjection (K ∪ L)ᶜ)).mp
    simp only [← Category.assoc, integralSupportRestriction_projection,
      integralProjection_sumRightProjection]
    rfl)

def integralSupportIntermediateSequenceIso (K L : Set X) :
    integralRelativeMayerVietoris Kᶜ Lᶜ ≅ integralSupportIntermediateSequence K L :=
  ShortComplex.isoMk (integralRelativeSetIso (Set.compl_union K L).symm)
    (Iso.refl _) (Iso.refl _) (by
      change (integralRelativeSetIso (Set.compl_union K L).symm).hom ≫
          integralSupportUnionMap K L = integralUnionRestriction Kᶜ Lᶜ ≫ 𝟙 _
      rw [Category.comp_id]
      apply (cancel_epi (integralRelativeProjection (Kᶜ ∩ Lᶜ))).mp
      apply biprod.hom_ext
      · simp only [Category.assoc, integralUnionRestriction,
          integralSupportUnionMap, biprod.lift_fst, integralRelativeRestriction_projection]
        rw [← Category.assoc, integralRelativeSetIso_projection,
          integralSupportRestriction_projection]
      · simp only [Category.assoc, integralUnionRestriction,
          integralSupportUnionMap, biprod.lift_snd, integralRelativeRestriction_projection]
        rw [← Category.assoc, integralRelativeSetIso_projection,
          integralSupportRestriction_projection]) (by
      simp [integralSupportIntermediateSequence, integralRelativeMayerVietoris])

theorem integralSupportIntermediateSequence_shortExact (K L : Set X) :
    (integralSupportIntermediateSequence K L).ShortExact :=
  ShortComplex.shortExact_of_iso (integralSupportIntermediateSequenceIso K L)
    (integralRelativeMayerVietoris_shortExact Kᶜ Lᶜ)

def integralSupportIntersectionHomologyIso
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat) :
    (integralSumQuotient Kᶜ Lᶜ).homology n ≅ integralSupportHomology (K ∩ L) n := by
  let : IsIso (homologyMap (integralSumComparison Kᶜ Lᶜ) n) :=
    integralSumComparison_homology_isIso Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n
  exact asIso (homologyMap (integralSumComparison Kᶜ Lᶜ) n) ≪≫
    (homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).mapIso
      (integralRelativeSetIso (Set.compl_inter K L).symm)

theorem integralSupportComparison_homology_isIso
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat) :
    IsIso (homologyMap (integralSupportComparison K L) n) := by
  let : IsIso (homologyMap (integralSumComparison Kᶜ Lᶜ) n) :=
    integralSumComparison_homology_isIso Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n
  rw [integralSupportComparison, homologyMap_comp]
  infer_instance

theorem integralHomologyBiprod_ext
    (C D : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat)
    {a b : (C ⊞ D).homology n}
    (h₁ : homologyMap (biprod.fst : C ⊞ D ⟶ C) n a =
      homologyMap (biprod.fst : C ⊞ D ⟶ C) n b)
    (h₂ : homologyMap (biprod.snd : C ⊞ D ⟶ D) n a =
      homologyMap (biprod.snd : C ⊞ D ⟶ D) n b) : a = b := by
  have ht : homologyMap (biprod.fst : C ⊞ D ⟶ C) n ≫ homologyMap biprod.inl n +
      homologyMap (biprod.snd : C ⊞ D ⟶ D) n ≫ homologyMap biprod.inr n = 𝟙 _ := by
    rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
      biprod.total, homologyMap_id]
  have he : homologyMap (biprod.inl : C ⟶ C ⊞ D) n
        (homologyMap (biprod.fst : C ⊞ D ⟶ C) n a) +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) n
        (homologyMap (biprod.snd : C ⊞ D ⟶ D) n a) = a :=
    congrArg (fun f => f a) ht
  have hf : homologyMap (biprod.inl : C ⟶ C ⊞ D) n
        (homologyMap (biprod.fst : C ⊞ D ⟶ C) n b) +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) n
        (homologyMap (biprod.snd : C ⊞ D ⟶ D) n b) = b :=
    congrArg (fun f => f b) ht
  rw [h₁, h₂] at he
  exact he.symm.trans hf

@[simp]
theorem integralSupportUnionMap_homology_fst (K L : Set X) (n : Nat) :
    homologyMap (integralSupportUnionMap K L) n ≫ homologyMap biprod.fst n =
      integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n := by
  rw [← homologyMap_comp, integralSupportUnionMap, biprod.lift_fst]
  rfl

@[simp]
theorem integralSupportUnionMap_homology_snd (K L : Set X) (n : Nat) :
    homologyMap (integralSupportUnionMap K L) n ≫ homologyMap biprod.snd n =
      integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n := by
  rw [← homologyMap_comp, integralSupportUnionMap, biprod.lift_snd]
  rfl

theorem exists_integralSupportHomology_union
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (a : integralSupportHomology K n) (b : integralSupportHomology L n)
    (hab : integralSupportHomologyRestriction (Set.inter_subset_left : K ∩ L ⊆ K) n a =
      integralSupportHomologyRestriction (Set.inter_subset_right : K ∩ L ⊆ L) n b) :
    ∃ c : integralSupportHomology (K ∪ L) n,
      integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n c = a ∧
      integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n c = b := by
  let C := integralSupportChains K
  let D := integralSupportChains L
  let v : (C ⊞ D).homology n :=
    homologyMap (biprod.inl : C ⟶ C ⊞ D) n a +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) n b
  have hfst : homologyMap (biprod.fst : C ⊞ D ⟶ C) n v = a := by
    simp [v, ← ConcreteCategory.comp_apply, ← homologyMap_comp]
  have hsnd : homologyMap (biprod.snd : C ⊞ D ⟶ D) n v = b := by
    simp [v, ← ConcreteCategory.comp_apply, ← homologyMap_comp]
  have hv : homologyMap (integralSumDifference Kᶜ Lᶜ) n v = 0 := by
    let := integralSupportComparison_homology_isIso K L hK hL n
    apply (ModuleCat.mono_iff_injective (homologyMap (integralSupportComparison K L) n)).mp
      inferInstance
    rw [map_zero, ← ConcreteCategory.comp_apply, ← homologyMap_comp,
      integralSupportComparison_difference]
    simp only [v, map_add, ← ConcreteCategory.comp_apply, ← homologyMap_comp,
      integralSupportDifference, biprod.inl_desc, biprod.inr_desc, homologyMap_neg]
    change (integralSupportHomologyRestriction (Set.inter_subset_left : K ∩ L ⊆ K) n).hom a +
      (-integralSupportHomologyRestriction (Set.inter_subset_right : K ∩ L ⊆ L) n).hom b = 0
    simpa only [ModuleCat.hom_neg, LinearMap.neg_apply, sub_eq_add_neg] using
      sub_eq_zero.mpr hab
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((integralSupportIntermediateSequence_shortExact K L).homology_exact₂ n) v hv
  change integralSupportHomology (K ∪ L) n at c
  change homologyMap (integralSupportUnionMap K L) n c = v at hc
  refine ⟨c, ?_, ?_⟩
  · have he := congrArg (homologyMap (biprod.fst : C ⊞ D ⟶ C) n) hc
    change homologyMap (biprod.fst : C ⊞ D ⟶ C) n
        (homologyMap (integralSupportUnionMap K L) n c) =
      homologyMap (biprod.fst : C ⊞ D ⟶ C) n v at he
    rw [← ConcreteCategory.comp_apply, integralSupportUnionMap_homology_fst, hfst] at he
    exact he
  · have he := congrArg (homologyMap (biprod.snd : C ⊞ D ⟶ D) n) hc
    change homologyMap (biprod.snd : C ⊞ D ⟶ D) n
        (homologyMap (integralSupportUnionMap K L) n c) =
      homologyMap (biprod.snd : C ⊞ D ⟶ D) n v at he
    rw [← ConcreteCategory.comp_apply, integralSupportUnionMap_homology_snd, hsnd] at he
    exact he

theorem integralSupportUnionMap_homology_mono
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (hI : IsZero (integralSupportHomology (K ∩ L) (n + 1))) :
    Mono (homologyMap (integralSupportUnionMap K L) n) := by
  have hQ : IsZero ((integralSumQuotient Kᶜ Lᶜ).homology (n + 1)) :=
    IsZero.of_iso hI (integralSupportIntersectionHomologyIso K L hK hL (n + 1))
  exact ((integralSupportIntermediateSequence_shortExact K L).homology_exact₁
    (n + 1) n rfl).mono_g (hQ.eq_zero_of_src _)

theorem integralSupportHomology_union_ext
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (hI : IsZero (integralSupportHomology (K ∩ L) (n + 1)))
    {a b : integralSupportHomology (K ∪ L) n}
    (h₁ : integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n a =
      integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n b)
    (h₂ : integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n a =
      integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n b) : a = b := by
  let := integralSupportUnionMap_homology_mono K L hK hL n hI
  apply (ModuleCat.mono_iff_injective (homologyMap (integralSupportUnionMap K L) n)).mp
    inferInstance
  apply integralHomologyBiprod_ext
  · simpa only [← ConcreteCategory.comp_apply,
      integralSupportUnionMap_homology_fst] using h₁
  · simpa only [← ConcreteCategory.comp_apply,
      integralSupportUnionMap_homology_snd] using h₂

theorem integralSupportHomology_union_isZero
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (hI : IsZero (integralSupportHomology (K ∩ L) (n + 1)))
    (hK₀ : IsZero (integralSupportHomology K n))
    (hL₀ : IsZero (integralSupportHomology L n)) :
    IsZero (integralSupportHomology (K ∪ L) n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => integralSupportHomology_union_ext K L hK hL n hI ?_ ?_⟩
  · exact (ModuleCat.isZero_iff_subsingleton.mp hK₀).elim _ _
  · exact (ModuleCat.isZero_iff_subsingleton.mp hL₀).elim _ _

end Poincare.Topology
