import PoincareConjecture.Proofs.M02.Topology.IntegralExcision
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexBiprod















set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def integralNestedInclusion {A B : Set X} (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a => ⟨a.val, h a.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def integralNestedChains {A B : Set X} (h : A ⊆ B) :
    integralChains A ⟶ integralChains B :=
  integralChainsFunctor.map (integralNestedInclusion h)

@[reassoc (attr := simp)]
theorem integralNestedChains_subspaceChains {A B : Set X} (h : A ⊆ B) :
    integralNestedChains h ≫ integralSubspaceChains B = integralSubspaceChains A := by
  rw [integralNestedChains, integralSubspaceChains, ← integralChainsFunctor.map_comp]
  rfl

abbrev integralNestedQuotient {A B : Set X} (h : A ⊆ B) :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralNestedChains h)

def integralNestedToRelative {A B : Set X} (h : A ⊆ B) :
    integralNestedQuotient h ⟶ integralRelativeChains A :=
  cokernel.desc (integralNestedChains h)
    (integralSubspaceChains B ≫ integralRelativeProjection A) (by
      rw [← Category.assoc, integralNestedChains_subspaceChains,
        cokernel.condition])

@[reassoc (attr := simp)]
theorem integralNestedToRelative_projection {A B : Set X} (h : A ⊆ B) :
    cokernel.π (integralNestedChains h) ≫ integralNestedToRelative h =
      integralSubspaceChains B ≫ integralRelativeProjection A :=
  cokernel.π_desc _ _ _

def integralRelativeRestriction {A B : Set X} (h : A ⊆ B) :
    integralRelativeChains A ⟶ integralRelativeChains B :=
  integralRelativeMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) A B from
    fun ⦃x⦄ hx => by rw [ContinuousMap.id_apply]; exact h hx)

@[reassoc (attr := simp)]
theorem integralRelativeRestriction_projection {A B : Set X} (h : A ⊆ B) :
    integralRelativeProjection A ≫ integralRelativeRestriction h =
      integralRelativeProjection B := by
  change integralRelativeProjection A ≫
    integralRelativeMap (ContinuousMap.id X) _ = integralRelativeProjection B
  have hm := integralRelativeMap_projection (ContinuousMap.id X)
    (A := A) (B := B)
    (show Set.MapsTo (ContinuousMap.id X) A B from
      fun ⦃x⦄ hx => by rw [ContinuousMap.id_apply]; exact h hx)
  rw [hm]
  change integralChainsFunctor.map (𝟙 (TopCat.of X)) ≫ integralRelativeProjection B = _
  simp

def integralPairInclusion (A B : Set X) :
    integralRelativeChains ((Subtype.val : B → X) ⁻¹' A) ⟶
      integralRelativeChains A :=
  integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := (Subtype.val : B → X) ⁻¹' A) (B := A)
      (show Set.MapsTo (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
        ((Subtype.val : B → X) ⁻¹' A) A from fun ⦃x⦄ hx => by exact hx)

@[reassoc (attr := simp)]
theorem integralPairInclusion_projection (A B : Set X) :
    integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A) ≫
        integralPairInclusion A B =
      integralSubspaceChains B ≫ integralRelativeProjection A := by
  change integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A) ≫
    integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)) _ = _
  have hm := integralRelativeMap_projection
    (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := (Subtype.val : B → X) ⁻¹' A) (B := A)
    (show Set.MapsTo (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      ((Subtype.val : B → X) ⁻¹' A) A from fun ⦃x⦄ hx => by exact hx)
  rw [hm]
  rfl

abbrev integralSumQuotient (A B : Set X) :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralPairInclusion A B)

abbrev integralSumProjection (A B : Set X) :
    integralRelativeChains A ⟶ integralSumQuotient A B :=
  cokernel.π (integralPairInclusion A B)

def integralSumAmbientProjection (A B : Set X) :
    integralChains X ⟶ integralSumQuotient A B :=
  integralRelativeProjection A ≫ integralSumProjection A B

@[reassoc (attr := simp)]
theorem integralSubspace_sumAmbientProjection_left (A B : Set X) :
    integralSubspaceChains A ≫ integralSumAmbientProjection A B = 0 := by
  simp [integralSumAmbientProjection, ← Category.assoc]

@[reassoc (attr := simp)]
theorem integralSubspace_sumAmbientProjection_right (A B : Set X) :
    integralSubspaceChains B ≫ integralSumAmbientProjection A B = 0 := by
  rw [integralSumAmbientProjection, ← Category.assoc,
    ← integralPairInclusion_projection, Category.assoc,
    cokernel.condition, comp_zero]

theorem integralProjection_surjective {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : C ⟶ D) (n : Nat) :
    Function.Surjective ((cokernel.π f).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem integralProjection_eq_zero_iff
    {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : C ⟶ D) (n : Nat) (x : D.X n) :
    (cokernel.π f).f n x = 0 ↔ ∃ y, f.f n y = x := by
  have h := (ShortComplex.cokernelSequence_exact f).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).mp h x
  · rintro ⟨y, rfl⟩
    exact congrArg (fun q => q.f n y) (cokernel.condition f)

theorem integralPairInclusion_injective (A B : Set X) (n : Nat) :
    Function.Injective ((integralPairInclusion A B).f n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨b, rfl⟩ := integralProjection_surjective
    (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) n x
  have hn := congrArg (fun f => f.f n b) (integralPairInclusion_projection A B)
  change (integralPairInclusion A B).f n
      ((integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A)).f n b) =
    (integralRelativeProjection A).f n ((integralSubspaceChains B).f n b) at hn
  rw [hn] at hx
  obtain ⟨a, ha⟩ := (integralProjection_eq_zero_iff
    (integralSubspaceChains A) n _).mp hx
  have hb : (integralSubspaceChains B).f n b ∈
      LinearMap.range ((integralSubspaceChains A).f n).hom := ⟨a, ha⟩
  have hb' : b ∈ LinearMap.range
      ((integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)).f n).hom :=
    (integralSubspaceChains_range_preimage A B n b).mp hb
  exact (integralProjection_eq_zero_iff
    (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) n _).mpr hb'

instance integralPairInclusion_mono (A B : Set X) :
    Mono (integralPairInclusion A B) :=
  HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).mpr (integralPairInclusion_injective A B n))

theorem integralSumAmbientProjection_eq_zero_iff (A B : Set X) (n : Nat)
    (x : (integralChains X).X n) :
    (integralSumAmbientProjection A B).f n x = 0 ↔
      ∃ a : (integralChains A).X n, ∃ b : (integralChains B).X n,
        x = (integralSubspaceChains A).f n a +
          (integralSubspaceChains B).f n b := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (integralProjection_eq_zero_iff
      (integralPairInclusion A B) n _).mp hx
    obtain ⟨b, rfl⟩ := integralProjection_surjective
      (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) n y
    have hn := congrArg (fun f => f.f n b) (integralPairInclusion_projection A B)
    change (integralPairInclusion A B).f n
        ((integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A)).f n b) =
      (integralRelativeProjection A).f n ((integralSubspaceChains B).f n b) at hn
    rw [hn] at hy
    have hz : (integralRelativeProjection A).f n
        (x - (integralSubspaceChains B).f n b) = 0 := by
      rw [map_sub, hy]
      exact sub_self _
    obtain ⟨a, ha⟩ := (integralProjection_eq_zero_iff
      (integralSubspaceChains A) n _).mp hz
    exact ⟨a, b, (sub_eq_iff_eq_add.mp ha.symm)⟩
  · rintro ⟨a, b, rfl⟩
    rw [map_add]
    have ha := congrArg (fun f => f.f n a)
      (integralSubspace_sumAmbientProjection_left A B)
    have hb := congrArg (fun f => f.f n b)
      (integralSubspace_sumAmbientProjection_right A B)
    exact (congrArg₂ (· + ·) ha hb).trans (zero_add 0)

def integralSumRightProjection (A B : Set X) :
    integralRelativeChains B ⟶ integralSumQuotient A B :=
  cokernel.desc (integralSubspaceChains B) (integralSumAmbientProjection A B)
    (integralSubspace_sumAmbientProjection_right A B)

@[reassoc (attr := simp)]
theorem integralProjection_sumRightProjection (A B : Set X) :
    integralRelativeProjection B ≫ integralSumRightProjection A B =
      integralSumAmbientProjection A B :=
  cokernel.π_desc _ _ _

def integralUnionRestriction (A B : Set X) :
    integralRelativeChains (A ∩ B) ⟶
      integralRelativeChains A ⊞ integralRelativeChains B :=
  biprod.lift
    (integralRelativeRestriction (Set.inter_subset_left : A ∩ B ⊆ A))
    (integralRelativeRestriction (Set.inter_subset_right : A ∩ B ⊆ B))

def integralSumDifference (A B : Set X) :
    integralRelativeChains A ⊞ integralRelativeChains B ⟶
      integralSumQuotient A B :=
  biprod.desc (integralSumProjection A B) (-integralSumRightProjection A B)

theorem integralUnionRestriction_sumDifference (A B : Set X) :
    integralUnionRestriction A B ≫ integralSumDifference A B = 0 := by
  rw [integralUnionRestriction, integralSumDifference, biprod.lift_desc,
    Preadditive.comp_neg, ← sub_eq_add_neg]
  apply sub_eq_zero.mpr
  apply (cancel_epi (integralRelativeProjection (A ∩ B))).mp
  simp only [← Category.assoc, integralRelativeRestriction_projection,
    integralProjection_sumRightProjection]
  rfl

def integralRelativeMayerVietoris (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralUnionRestriction A B) (integralSumDifference A B)
    (integralUnionRestriction_sumDifference A B)

theorem integralBiprod_component_ext {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    {n : Nat} {x y : (C ⊞ D).X n}
    (h₁ : (biprod.fst : C ⊞ D ⟶ C).f n x =
      (biprod.fst : C ⊞ D ⟶ C).f n y)
    (h₂ : (biprod.snd : C ⊞ D ⟶ D).f n x =
      (biprod.snd : C ⊞ D ⟶ D).f n y) :
    x = y := by
  have ht (z : (C ⊞ D).X n) := congrArg (fun f => f z) (biprod_total_f C D n)
  exact (ht x).symm.trans ((congrArg₂ (· + ·)
    (congrArg ((biprod.inl : C ⟶ C ⊞ D).f n) h₁)
    (congrArg ((biprod.inr : D ⟶ C ⊞ D).f n) h₂)).trans (ht y))

theorem integralSumDifference_apply (A B : Set X) (n : Nat)
    (y : (integralRelativeChains A ⊞ integralRelativeChains B).X n) :
    (integralSumDifference A B).f n y =
      (integralSumProjection A B).f n
        ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
          integralRelativeChains A).f n y) -
      (integralSumRightProjection A B).f n
        ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
          integralRelativeChains B).f n y) := by
  have h : integralSumDifference A B =
      biprod.fst ≫ integralSumProjection A B -
        biprod.snd ≫ integralSumRightProjection A B := by
    apply biprod.hom_ext' <;> simp [integralSumDifference, Preadditive.comp_sub]
  exact congrArg (fun f => f.f n y) h

theorem integralUnionRestriction_injective (A B : Set X) (n : Nat) :
    Function.Injective ((integralUnionRestriction A B).f n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨c, rfl⟩ := integralProjection_surjective
    (integralSubspaceChains (A ∩ B)) n x
  have hA : (integralRelativeProjection A).f n c = 0 := by
    have h := congrArg (fun f => f.f n c)
      (show integralRelativeProjection (A ∩ B) ≫ integralUnionRestriction A B ≫
        biprod.fst = integralRelativeProjection A by
        rw [integralUnionRestriction, biprod.lift_fst,
          integralRelativeRestriction_projection])
    exact h.symm.trans ((congrArg
      ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains A).f n) hx).trans (map_zero _))
  have hB : (integralRelativeProjection B).f n c = 0 := by
    have h := congrArg (fun f => f.f n c)
      (show integralRelativeProjection (A ∩ B) ≫ integralUnionRestriction A B ≫
        biprod.snd = integralRelativeProjection B by
        rw [integralUnionRestriction, biprod.lift_snd,
          integralRelativeRestriction_projection])
    exact h.symm.trans ((congrArg
      ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains B).f n) hx).trans (map_zero _))
  obtain ⟨a, ha⟩ := (integralProjection_eq_zero_iff
    (integralSubspaceChains A) n _).mp hA
  obtain ⟨b, hb⟩ := (integralProjection_eq_zero_iff
    (integralSubspaceChains B) n _).mp hB
  have hc : c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ⊓
      LinearMap.range ((integralSubspaceChains B).f n).hom :=
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [integralSubspaceChains_range_inf] at hc
  exact (integralProjection_eq_zero_iff
    (integralSubspaceChains (A ∩ B)) n c).mpr hc

theorem integralRelativeMayerVietoris_shortExact (A B : Set X) :
    (integralRelativeMayerVietoris A B).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    let y' : (integralRelativeChains A ⊞ integralRelativeChains B).X n := y
    obtain ⟨u, hu⟩ := integralProjection_surjective
      (integralSubspaceChains A) n
      ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains A).f n y')
    obtain ⟨v, hv⟩ := integralProjection_surjective
      (integralSubspaceChains B) n
      ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains B).f n y')
    have hdiff : (integralSumAmbientProjection A B).f n (u - v) = 0 := by
      change (integralSumDifference A B).f n y' = 0 at hy
      have happly := integralSumDifference_apply A B n y'
      rw [happly, ← hu, ← hv] at hy
      have hA : (integralSumProjection A B).f n
          ((integralRelativeProjection A).f n u) =
          (integralSumAmbientProjection A B).f n u := rfl
      have hB := congrArg (fun f => f.f n v)
        (integralProjection_sumRightProjection A B)
      change (integralSumRightProjection A B).f n
          ((integralRelativeProjection B).f n v) =
        (integralSumAmbientProjection A B).f n v at hB
      rw [map_sub, ← hA, ← hB]
      exact hy
    obtain ⟨a, b, hab⟩ :=
      (integralSumAmbientProjection_eq_zero_iff A B n (u - v)).mp hdiff
    let w := u - (integralSubspaceChains A).f n a
    have hw : w = v + (integralSubspaceChains B).f n b := by
      dsimp [w]
      rw [sub_eq_iff_eq_add.mp hab]
      abel
    refine ⟨(integralRelativeProjection (A ∩ B)).f n w, ?_⟩
    apply integralBiprod_component_ext
    · have h := congrArg (fun f => f.f n w)
        (show integralRelativeProjection (A ∩ B) ≫ integralUnionRestriction A B ≫
          biprod.fst = integralRelativeProjection A by
          rw [integralUnionRestriction, biprod.lift_fst,
            integralRelativeRestriction_projection])
      change (biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains A).f n
        ((integralUnionRestriction A B).f n
          ((integralRelativeProjection (A ∩ B)).f n w)) = _
      refine h.trans ?_
      change (integralRelativeProjection A).f n
        (u - (integralSubspaceChains A).f n a) = _
      rw [map_sub,
        (integralProjection_eq_zero_iff (integralSubspaceChains A) n _).mpr ⟨a, rfl⟩,
        sub_zero, hu]
    · have h := congrArg (fun f => f.f n w)
        (show integralRelativeProjection (A ∩ B) ≫ integralUnionRestriction A B ≫
          biprod.snd = integralRelativeProjection B by
          rw [integralUnionRestriction, biprod.lift_snd,
            integralRelativeRestriction_projection])
      change (biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains B).f n
        ((integralUnionRestriction A B).f n
          ((integralRelativeProjection (A ∩ B)).f n w)) = _
      refine h.trans ?_
      rw [hw, map_add,
        (integralProjection_eq_zero_iff (integralSubspaceChains B) n _).mpr ⟨b, rfl⟩,
        add_zero, hv]
  · exact (ModuleCat.mono_iff_injective _).mpr
      (integralUnionRestriction_injective A B n)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨a, rfl⟩ := integralProjection_surjective (integralPairInclusion A B) n z
    refine ⟨(biprod.inl : integralRelativeChains A ⟶ _).f n a, ?_⟩
    exact congrArg (fun f => f.f n a)
      (show biprod.inl ≫ integralSumDifference A B = integralSumProjection A B by
        simp [integralSumDifference])

def integralSumComparison (A B : Set X) :
    integralSumQuotient A B ⟶ integralRelativeChains (A ∪ B) :=
  cokernel.desc (integralPairInclusion A B)
    (integralRelativeRestriction (Set.subset_union_left : A ⊆ A ∪ B)) (by
      apply (cancel_epi
        (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
      rw [← Category.assoc, integralPairInclusion_projection, Category.assoc,
        integralRelativeRestriction_projection,
        ← integralNestedChains_subspaceChains
          (Set.subset_union_right : B ⊆ A ∪ B), Category.assoc,
        cokernel.condition]
      simp
    )

@[reassoc (attr := simp)]
theorem integralSumProjection_comparison (A B : Set X) :
    integralSumProjection A B ≫ integralSumComparison A B =
      integralRelativeRestriction (Set.subset_union_left : A ⊆ A ∪ B) :=
  cokernel.π_desc _ _ _

end PoincareConjecture.Proofs.M02.Topology
