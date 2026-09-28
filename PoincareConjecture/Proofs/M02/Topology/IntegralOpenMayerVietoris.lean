import PoincareConjecture.Proofs.M02.Topology.IntegralMayerVietoris

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def integralCoverMemberChains {I : Type v} (U : I → Set X)
    (A : Set X) (i : I) (hi : A ⊆ U i) :
    integralChains A ⟶ integralSmallChainComplex U where
  f n := by
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    exact ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U n)
      ((integralSubspaceChains A).f n).hom (fun c =>
        integralSubspaceChains_range_le_small U A i hi n ⟨c, rfl⟩))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f => f c) ((integralSubspaceChains A).comm i j)

@[reassoc (attr := simp)]
theorem integralCoverMemberChains_inclusion {I : Type v} (U : I → Set X)
    (A : Set X) (i : I) (hi : A ⊆ U i) :
    integralCoverMemberChains U A i hi ≫ integralSmallChainInclusion U =
      integralSubspaceChains A := by
  ext n c
  rfl

abbrev integralBinaryCover (A B : Set X) : Bool → Set X :=
  fun b => if b then A else B

def integralOpenDifference (A B : Set X) :
    integralChains ↥(A ∩ B) ⟶ integralChains A ⊞ integralChains B :=
  biprod.lift
    (integralNestedChains (Set.inter_subset_left : A ∩ B ⊆ A))
    (-integralNestedChains (Set.inter_subset_right : A ∩ B ⊆ B))

def integralOpenSum (A B : Set X) :
    integralChains A ⊞ integralChains B ⟶
      integralSmallChainComplex (integralBinaryCover A B) :=
  biprod.desc
    (integralCoverMemberChains (integralBinaryCover A B) A true (fun _ h => h))
    (integralCoverMemberChains (integralBinaryCover A B) B false (fun _ h => h))

@[reassoc (attr := simp)]
theorem integralOpenSum_inclusion (A B : Set X) :
    integralOpenSum A B ≫ integralSmallChainInclusion (integralBinaryCover A B) =
      biprod.desc (integralSubspaceChains A) (integralSubspaceChains B) := by
  apply biprod.hom_ext' <;> simp [integralOpenSum]

@[reassoc (attr := simp)]
theorem integralOpenDifference_sum (A B : Set X) :
    integralOpenDifference A B ≫ integralOpenSum A B = 0 := by
  let := integralSmallChainInclusion_mono (integralBinaryCover A B)
  apply (cancel_mono (integralSmallChainInclusion (integralBinaryCover A B))).mp
  rw [Category.assoc, integralOpenSum_inclusion, zero_comp]
  simp [integralOpenDifference, biprod.lift_desc, Preadditive.neg_comp]

def integralOpenChainSequence (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralOpenDifference A B) (integralOpenSum A B)
    (integralOpenDifference_sum A B)

theorem integralNestedChains_injective {A B : Set X} (h : A ⊆ B) (n : Nat) :
    Function.Injective ((integralNestedChains h).f n) := by
  let := integralSubspaceChains_mono A
  intro a b hab
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains A).f n)).mp inferInstance
  have hcomp := congrArg (fun f => f.f n) (integralNestedChains_subspaceChains h)
  exact (congrArg (fun f => f a) hcomp).symm.trans
    ((congrArg ((integralSubspaceChains B).f n) hab).trans
      (congrArg (fun f => f b) hcomp))

theorem integralOpenDifference_injective (A B : Set X) (n : Nat) :
    Function.Injective ((integralOpenDifference A B).f n) := by
  intro a b hab
  apply integralNestedChains_injective (Set.inter_subset_left : A ∩ B ⊆ A) n
  have h := congrArg ((biprod.fst : integralChains A ⊞ integralChains B ⟶ _).f n) hab
  have hf := congrArg (fun f => f.f n)
    (show integralOpenDifference A B ≫ biprod.fst =
      integralNestedChains (Set.inter_subset_left : A ∩ B ⊆ A) by
      simp [integralOpenDifference])
  exact (congrArg (fun f => f a) hf).symm.trans
    (h.trans (congrArg (fun f => f b) hf))

theorem integralOpenSum_inclusion_apply (A B : Set X) (n : Nat)
    (y : (integralChains A ⊞ integralChains B).X n) :
    (integralSmallChainInclusion (integralBinaryCover A B)).f n
      ((integralOpenSum A B).f n y) =
    (integralSubspaceChains A).f n
      ((biprod.fst : integralChains A ⊞ integralChains B ⟶ integralChains A).f n y) +
    (integralSubspaceChains B).f n
      ((biprod.snd : integralChains A ⊞ integralChains B ⟶ integralChains B).f n y) := by
  have h : integralOpenSum A B ≫
      integralSmallChainInclusion (integralBinaryCover A B) =
      biprod.fst ≫ integralSubspaceChains A + biprod.snd ≫ integralSubspaceChains B := by
    rw [integralOpenSum_inclusion]
    apply biprod.hom_ext' <;> simp [Preadditive.comp_add]
  exact congrArg (fun f => f.f n y) h

theorem integralOpenChainSequence_shortExact (A B : Set X) :
    (integralOpenChainSequence A B).ShortExact := by
  let := integralSubspaceChains_mono A
  let := integralSubspaceChains_mono B
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    let a := (biprod.fst : integralChains A ⊞ integralChains B ⟶ integralChains A).f n y
    let b := (biprod.snd : integralChains A ⊞ integralChains B ⟶ integralChains B).f n y
    have hz : (integralSubspaceChains A).f n a + (integralSubspaceChains B).f n b = 0 := by
      have h := integralOpenSum_inclusion_apply A B n y
      change (integralOpenSum A B).f n y = 0 at hy
      rw [hy, map_zero] at h
      exact h.symm
    have ha : (integralSubspaceChains A).f n a ∈
        LinearMap.range ((integralSubspaceChains A).f n).hom ⊓
          LinearMap.range ((integralSubspaceChains B).f n).hom := by
      refine ⟨⟨a, rfl⟩, ⟨-b, ?_⟩⟩
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left hz).symm
    rw [integralSubspaceChains_range_inf] at ha
    obtain ⟨c, hc⟩ := ha
    refine ⟨c, ?_⟩
    apply integralBiprod_component_ext
    · have hf := congrArg (fun f => f.f n c)
        (show integralOpenDifference A B ≫ biprod.fst =
          integralNestedChains (Set.inter_subset_left : A ∩ B ⊆ A) by
          simp [integralOpenDifference])
      change (biprod.fst : integralChains A ⊞ integralChains B ⟶ integralChains A).f n
        ((integralOpenDifference A B).f n c) = a
      refine hf.trans ?_
      apply (ModuleCat.mono_iff_injective ((integralSubspaceChains A).f n)).mp inferInstance
      exact (congrArg (fun f => f.f n c)
        (integralNestedChains_subspaceChains (Set.inter_subset_left : A ∩ B ⊆ A))).trans hc
    · have hf := congrArg (fun f => f.f n c)
        (show integralOpenDifference A B ≫ biprod.snd =
          -integralNestedChains (Set.inter_subset_right : A ∩ B ⊆ B) by
          simp [integralOpenDifference])
      change (biprod.snd : integralChains A ⊞ integralChains B ⟶ integralChains B).f n
        ((integralOpenDifference A B).f n c) = b
      refine hf.trans ?_
      apply (ModuleCat.mono_iff_injective ((integralSubspaceChains B).f n)).mp inferInstance
      change (integralSubspaceChains B).f n
        (-((integralNestedChains (Set.inter_subset_right : A ∩ B ⊆ B)).f n c)) = _
      rw [map_neg]
      have hc' := congrArg (fun f => f.f n c)
        (integralNestedChains_subspaceChains (Set.inter_subset_right : A ∩ B ⊆ B))
      change (integralSubspaceChains B).f n
        ((integralNestedChains (Set.inter_subset_right : A ∩ B ⊆ B)).f n c) =
          (integralSubspaceChains (A ∩ B)).f n c at hc'
      rw [hc', hc]
      exact neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_left hz)
  · exact (ModuleCat.mono_iff_injective _).mpr (integralOpenDifference_injective A B n)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro z
    let c : (integralChains X).X n := z.val
    have hz : c ∈ integralSmallChains (integralBinaryCover A B) n := z.property
    rw [integralSmallChains_two_eq_sup] at hz
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hz
    refine ⟨(biprod.inl : integralChains A ⟶ integralChains A ⊞ integralChains B).f n a +
      (biprod.inr : integralChains B ⟶ integralChains A ⊞ integralChains B).f n b, ?_⟩
    apply Subtype.ext
    change (integralSmallChainInclusion (integralBinaryCover A B)).f n
      ((integralOpenSum A B).f n _) = z.val
    rw [map_add, map_add]
    have hA := congrArg (fun f => f.f n a)
      (show biprod.inl ≫ integralOpenSum A B ≫
        integralSmallChainInclusion (integralBinaryCover A B) = integralSubspaceChains A by
        simp)
    have hB := congrArg (fun f => f.f n b)
      (show biprod.inr ≫ integralOpenSum A B ≫
        integralSmallChainInclusion (integralBinaryCover A B) = integralSubspaceChains B by
        simp)
    exact (congrArg₂ (· + ·) hA hB).trans hab

theorem integralOpenComparison_quasiIso (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    QuasiIso (integralSmallChainInclusion (integralBinaryCover A B)) := by
  apply integralSmallChainInclusion_quasiIso
  · intro b
    cases b <;> assumption
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x ∈ A ∪ B := hcover ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩

def integralOpenHomologyIso (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : Nat) :
    (integralSmallChainComplex (integralBinaryCover A B)).homology n ≅
      integralHomology X n := by
  let := integralOpenComparison_quasiIso A B hA hB hcover
  exact asIso (homologyMap (integralSmallChainInclusion (integralBinaryCover A B)) n)

def integralOpenHomologyConnecting (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : Nat) :
    integralHomology X (n + 1) ⟶ integralHomology ↥(A ∩ B) n :=
  (integralOpenHomologyIso A B hA hB hcover (n + 1)).inv ≫
    (integralOpenChainSequence_shortExact A B).δ (n + 1) n rfl

theorem integralOpenHomologyConnecting_two_eq
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) {T : ModuleCat.{u} Int}
    (z : T ⟶ (integralSmallChainComplex (integralBinaryCover A B)).X 2)
    (hz : z ≫ (integralSmallChainComplex (integralBinaryCover A B)).d 2 1 = 0)
    (b : T ⟶ (integralChains A ⊞ integralChains B).X 2)
    (hb : b ≫ (integralOpenSum A B).f 2 = z)
    (a : T ⟶ (integralChains ↥(A ∩ B)).X 1)
    (ha : a ≫ (integralChains ↥(A ∩ B)).d 1 0 = 0)
    (hboundary : a ≫ (integralOpenDifference A B).f 1 =
      b ≫ (integralChains A ⊞ integralChains B).d 2 1) :
    (integralSmallChainComplex (integralBinaryCover A B)).liftCycles z 1
        ((ComplexShape.down Nat).next_eq' (show (ComplexShape.down Nat).Rel 2 1 from rfl)) hz ≫
      (integralSmallChainComplex (integralBinaryCover A B)).homologyπ 2 ≫
      homologyMap (integralSmallChainInclusion (integralBinaryCover A B)) 2 ≫
      integralOpenHomologyConnecting A B hA hB hcover 1 =
    (integralChains ↥(A ∩ B)).liftCycles a 0
        ((ComplexShape.down Nat).next_eq' (show (ComplexShape.down Nat).Rel 1 0 from rfl)) ha ≫
      (integralChains ↥(A ∩ B)).homologyπ 1 := by
  let S := integralOpenChainSequence A B
  let hS := integralOpenChainSequence_shortExact A B
  let e := integralOpenHomologyIso A B hA hB hcover 2
  have he := hS.δ_eq 2 1 rfl z hz b hb a hboundary 0
    ((ComplexShape.down Nat).next_eq' (show (ComplexShape.down Nat).Rel 1 0 from rfl))
  change S.X₃.liftCycles z 1 _ hz ≫ S.X₃.homologyπ 2 ≫
    e.hom ≫ e.inv ≫ hS.δ 2 1 rfl = _
  rw [Iso.hom_inv_id_assoc]
  exact he

end PoincareConjecture.Proofs.M02.Topology
