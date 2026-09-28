import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ModTwoMayerVietorisChains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open Poincare.Topology

universe u

namespace PoincareConjecture.M76.ModTwoMayerVietoris

variable {X : Type u} [TopologicalSpace X]

abbrev homology (Y : Type u) [TopologicalSpace Y] (n : ℕ) : ModuleCat.{u} (ZMod 2) :=
  (chains Y).homology n

abbrev homologyMapOf {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) := homologyMap (chainMap f) n

def homologyIso (Y : Type u) [TopologicalSpace Y] (n : ℕ) :
    homology Y n ≅ (chainChange.obj (integralChains Y)).homology n :=
  (homologyFunctor _ _ n).mapIso (chainIso Y)

@[reassoc]
theorem homologyIso_naturality {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) :
    homologyMapOf f n ≫ (homologyIso Z n).hom =
      (homologyIso Y n).hom ≫
        homologyMap (chainChange.map (integralChainsFunctor.map (TopCat.ofHom f))) n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n ≫ homologyMap _ n
  rw [← homologyMap_comp, ← homologyMap_comp, chainIso_naturality]

@[reassoc]
theorem homologyIso_inv_naturality {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) :
    homologyMap (chainChange.map (integralChainsFunctor.map (TopCat.ofHom f))) n ≫
      (homologyIso Z n).inv = (homologyIso Y n).inv ≫ homologyMapOf f n := by
  apply (cancel_epi (homologyIso Y n).hom).mp
  simp only [Iso.hom_inv_id_assoc, ← homologyIso_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

def difference (A B : Set X) (n : ℕ) :
    homology ↥(A ∩ B) n ⟶ homology A n ⊞ homology B n :=
  biprod.lift
    (homologyMapOf ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩ n)
    (-homologyMapOf ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩ n)

def sum (A B : Set X) (n : ℕ) :
    homology A n ⊞ homology B n ⟶ homology X n :=
  biprod.desc
    (homologyMapOf ⟨Subtype.val, continuous_subtype_val⟩ n)
    (homologyMapOf ⟨Subtype.val, continuous_subtype_val⟩ n)

def pairIso (A B : Set X) (n : ℕ) :
    (chainChange.obj (integralChains A ⊞ integralChains B)).homology n ≅
      homology A n ⊞ homology B n where
  hom := biprod.lift
    (homologyMap (chainChange.map biprod.fst) n ≫ (homologyIso A n).inv)
    (homologyMap (chainChange.map biprod.snd) n ≫ (homologyIso B n).inv)
  inv := biprod.desc
    ((homologyIso A n).hom ≫ homologyMap (chainChange.map biprod.inl) n)
    ((homologyIso B n).hom ≫ homologyMap (chainChange.map biprod.inr) n)
  hom_inv_id := by
    rw [biprod.lift_desc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← homologyMap_comp, ← homologyMap_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← homologyMap_add, ← Functor.map_add, biprod.total,
      CategoryTheory.Functor.map_id, homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [Category.assoc, ← homologyMap_comp_assoc, ← Functor.map_comp]

def comparisonIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (openChainSequence A B).X₃.homology n ≅ homology X n := by
  let := openComparison_quasiIso A B hA hB hcover
  exact asIso (homologyMap (chainChange.map
    (integralSmallChainInclusion (integralBinaryCover A B))) n) ≪≫
      (homologyIso X n).symm

@[reassoc]
theorem difference_transport (A B : Set X) (n : ℕ) :
    homologyMap (openChainSequence A B).f n ≫ (pairIso A B n).hom =
      (homologyIso ↥(A ∩ B) n).inv ≫ difference A B n := by
  apply biprod.hom_ext
  · simpa [pairIso, difference, openChainSequence, integralOpenChainSequence,
      integralOpenDifference, Category.assoc, ← homologyMap_comp_assoc,
      ← Functor.map_comp, integralNestedChains, integralNestedInclusion] using
      homologyIso_inv_naturality
        (⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩ : C(↥(A ∩ B), A)) n
  · simpa [pairIso, difference, openChainSequence, integralOpenChainSequence,
      integralOpenDifference, Category.assoc, ← homologyMap_comp_assoc,
      ← Functor.map_comp, homologyMap_neg, integralNestedChains, integralNestedInclusion] using
      congrArg Neg.neg (homologyIso_inv_naturality
        (⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩ : C(↥(A ∩ B), B)) n)

@[reassoc]
theorem sum_transport (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (pairIso A B n).hom ≫ sum A B n =
      homologyMap (openChainSequence A B).g n ≫
        (comparisonIso A B hA hB hcover n).hom := by
  change _ = homologyMap (chainChange.map (integralOpenSum A B)) n ≫
    homologyMap (chainChange.map (integralSmallChainInclusion (integralBinaryCover A B))) n ≫
      (homologyIso X n).inv
  rw [← homologyMap_comp_assoc, ← Functor.map_comp, integralOpenSum_inclusion]
  simp only [pairIso, sum, biprod.lift_desc, Category.assoc]
  rw [← homologyIso_inv_naturality, ← homologyIso_inv_naturality]
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
    ← homologyMap_comp, ← homologyMap_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← homologyMap_add, ← Functor.map_add]
  congr 2
  congr 1
  apply biprod.hom_ext' <;> simp <;> rfl

def connecting (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    homology X (n + 1) ⟶ homology ↥(A ∩ B) n :=
  (comparisonIso A B hA hB hcover (n + 1)).inv ≫
    (openChainSequence_shortExact A B).δ (n + 1) n rfl ≫
      (homologyIso ↥(A ∩ B) n).inv

@[reassoc]
theorem connecting_transport (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (comparisonIso A B hA hB hcover (n + 1)).hom ≫
      connecting A B hA hB hcover n =
    (openChainSequence_shortExact A B).δ (n + 1) n rfl ≫
      (homologyIso ↥(A ∩ B) n).inv := by
  simp [connecting]

theorem difference_sum (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) : difference A B n ≫ sum A B n = 0 := by
  apply (cancel_epi (homologyIso ↥(A ∩ B) n).inv).mp
  rw [← Category.assoc, ← difference_transport, Category.assoc,
    sum_transport A B hA hB hcover, ← Category.assoc, ← homologyMap_comp,
    (openChainSequence A B).zero, homologyMap_zero, zero_comp, comp_zero]

theorem sum_connecting (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    sum A B (n + 1) ≫ connecting A B hA hB hcover n = 0 := by
  apply (cancel_epi (pairIso A B (n + 1)).hom).mp
  rw [← Category.assoc, sum_transport A B hA hB hcover,
    Category.assoc, connecting_transport, ← Category.assoc,
    (openChainSequence_shortExact A B).comp_δ, zero_comp, comp_zero]

theorem connecting_difference (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    connecting A B hA hB hcover n ≫ difference A B n = 0 := by
  apply (cancel_epi (comparisonIso A B hA hB hcover (n + 1)).hom).mp
  rw [← Category.assoc, connecting_transport, Category.assoc,
    ← difference_transport, ← Category.assoc,
    (openChainSequence_shortExact A B).δ_comp, zero_comp, comp_zero]

theorem exact_pair (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (difference_sum A B hA hB hcover n)).Exact := by
  let S := openChainSequence A B
  let e := ShortComplex.isoMk
    (homologyIso ↥(A ∩ B) n).symm (pairIso A B n)
    (comparisonIso A B hA hB hcover n)
    (S₁ := ShortComplex.mk (homologyMap S.f n) (homologyMap S.g n)
      (by rw [← homologyMap_comp, S.zero, homologyMap_zero]))
    (S₂ := ShortComplex.mk _ _ (difference_sum A B hA hB hcover n))
    (difference_transport A B n).symm (sum_transport A B hA hB hcover n)
  exact ShortComplex.exact_of_iso e ((openChainSequence_shortExact A B).homology_exact₂ n)

theorem exact_ambient (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (sum_connecting A B hA hB hcover n)).Exact := by
  let hS := openChainSequence_shortExact A B
  let e := ShortComplex.isoMk
    (pairIso A B (n + 1)) (comparisonIso A B hA hB hcover (n + 1))
    (homologyIso ↥(A ∩ B) n).symm
    (S₁ := ShortComplex.mk _ _ (hS.comp_δ (n + 1) n rfl))
    (S₂ := ShortComplex.mk _ _ (sum_connecting A B hA hB hcover n))
    (sum_transport A B hA hB hcover (n + 1))
    (connecting_transport A B hA hB hcover n)
  exact ShortComplex.exact_of_iso e (hS.homology_exact₃ (n + 1) n rfl)

theorem exact_intersection (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (connecting_difference A B hA hB hcover n)).Exact := by
  let hS := openChainSequence_shortExact A B
  let e := ShortComplex.isoMk
    (comparisonIso A B hA hB hcover (n + 1))
    (homologyIso ↥(A ∩ B) n).symm (pairIso A B n)
    (S₁ := ShortComplex.mk _ _ (hS.δ_comp (n + 1) n rfl))
    (S₂ := ShortComplex.mk _ _ (connecting_difference A B hA hB hcover n))
    (connecting_transport A B hA hB hcover n) (difference_transport A B n).symm
  exact ShortComplex.exact_of_iso e (hS.homology_exact₁ (n + 1) n rfl)

theorem sum_injective_of_intersection_h1_zero (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (hzero : IsZero (homology ↥(A ∩ B) 1)) :
    Function.Injective (sum A B 1) := by
  let S := ShortComplex.mk _ _ (difference_sum A B hA hB hcover 1)
  have hmono : Mono S.g := (S.exact_iff_mono (hzero.eq_of_src S.f 0)).mp
    (exact_pair A B hA hB hcover 1)
  exact (ModuleCat.mono_iff_injective S.g).mp hmono

theorem connecting_range_eq_h0_kernel (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    LinearMap.range (connecting A B hA hB hcover 0).hom =
      LinearMap.ker (difference A B 0).hom :=
  (exact_intersection A B hA hB hcover 0).moduleCat_range_eq_ker

def connectingToKernel (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    homology X 1 ⟶ ModuleCat.of (ZMod 2) (LinearMap.ker (difference A B 0).hom) :=
  ModuleCat.ofHom ((connecting A B hA hB hcover 0).hom.codRestrict _ (by
    intro x
    exact congrArg (fun f => f x) (connecting_difference A B hA hB hcover 0)))

theorem connectingToKernel_surjective (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    Function.Surjective (connectingToKernel A B hA hB hcover) := by
  intro y
  have hy : y.val ∈ LinearMap.range (connecting A B hA hB hcover 0).hom := by
    rw [connecting_range_eq_h0_kernel]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem sum_connectingToKernel (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    sum A B 1 ≫ connectingToKernel A B hA hB hcover = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f => f x) (sum_connecting A B hA hB hcover 0)

theorem h1_kernel_shortExact (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (hzero : IsZero (homology ↥(A ∩ B) 1)) :
    (ShortComplex.mk _ _ (sum_connectingToKernel A B hA hB hcover)).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    have hy' : connecting A B hA hB hcover 0 y = 0 :=
      congrArg Subtype.val hy
    exact ((ShortComplex.moduleCat_exact_iff _).mp
      (exact_ambient A B hA hB hcover 0)) y hy'
  · exact (ModuleCat.mono_iff_injective _).mpr
      (sum_injective_of_intersection_h1_zero A B hA hB hcover hzero)
  · exact (ModuleCat.epi_iff_surjective _).mpr
      (connectingToKernel_surjective A B hA hB hcover)

end PoincareConjecture.M76.ModTwoMayerVietoris
