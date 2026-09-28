import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SubcomplexChainExact
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenMayerVietoris
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor











set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v w

namespace PoincareConjecture.Proofs.M59

open M02.Topology

set_option backward.isDefEq.respectTransparency false in
private theorem quasiIso_biprod_map
    {C : Type v} [Category.{w} C] [Abelian C]
    {K₁ K₂ L₁ L₂ : ChainComplex C ℕ} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    [QuasiIso f] [QuasiIso g] : QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor C (ComplexShape.down ℕ) n
  let : H.Additive := by dsimp [H]; infer_instance
  let : PreservesFiniteBiproducts H := Functor.preservesFiniteBiproductsOfAdditive H
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have heq : H.map (biprod.map f g) =
      (H.mapBiprod K₁ K₂).hom ≫ biprod.map (H.map f) (H.map g) ≫
        (H.mapBiprod L₁ L₂).inv := by
    apply (cancel_mono (H.mapBiprod L₁ L₂).hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext <;>
      simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
        biprod.lift_snd, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, ← H.map_comp]
  change IsIso (H.map (biprod.map f g))
  rw [heq]
  let : IsIso (H.map f) := inferInstanceAs (IsIso (homologyMap f n))
  let : IsIso (H.map g) := inferInstanceAs (IsIso (homologyMap g n))
  let : IsIso (biprod.map (H.map f) (H.map g)) :=
    inferInstanceAs (IsIso (biprod.mapIso (asIso (H.map f)) (asIso (H.map g))).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in




theorem simplicialComparison_quasiIso_of_openCover
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {D : SSet.{u}} {D₁ D₂ D₃ D₄ : D.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq D₁ D₂ D₃ D₄)
    (χ₁ : D₁.toSSet ⟶ TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))
    (χ₂ : D₂.toSSet ⟶ TopCat.toSSet.obj (TopCat.of U))
    (χ₃ : D₃.toSSet ⟶ TopCat.toSSet.obj (TopCat.of V))
    (χ₄ : D₄.toSSet ⟶ TopCat.toSSet.obj (TopCat.of X))
    (h₁₂ : SSet.Subcomplex.homOfLE sq.le₁₂ ≫ χ₂ =
      χ₁ ≫ TopCat.toSSet.map (integralNestedInclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
    (h₁₃ : SSet.Subcomplex.homOfLE sq.le₁₃ ≫ χ₃ =
      χ₁ ≫ TopCat.toSSet.map (integralNestedInclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
    (h₂₄ : SSet.Subcomplex.homOfLE sq.le₂₄ ≫ χ₄ =
      χ₂ ≫ TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))))
    (h₃₄ : SSet.Subcomplex.homOfLE sq.le₃₄ ≫ χ₄ =
      χ₃ ≫ TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))))
    (hχ₁ : QuasiIso (SSet.chainComplexMap χ₁ integralCoefficient.{u}))
    (hχ₂ : QuasiIso (SSet.chainComplexMap χ₂ integralCoefficient.{u}))
    (hχ₃ : QuasiIso (SSet.chainComplexMap χ₃ integralCoefficient.{u})) :
    QuasiIso (SSet.chainComplexMap χ₄ integralCoefficient.{u}) := by
  let F := (SSet.chainComplexFunctor (ModuleCat.{u} Int)).obj integralCoefficient
  let j₁₂ := F.map (SSet.Subcomplex.homOfLE sq.le₁₂)
  let j₁₃ := F.map (SSet.Subcomplex.homOfLE sq.le₁₃)
  let j₂₄ := F.map (SSet.Subcomplex.homOfLE sq.le₂₄)
  let j₃₄ := F.map (SSet.Subcomplex.homOfLE sq.le₃₄)
  let f₁ := F.map χ₁
  let f₂ := F.map χ₂
  let f₃ := F.map χ₃
  let f₄ := F.map χ₄
  have H₁₂ : j₁₂ ≫ f₂ = f₁ ≫
      integralNestedChains (Set.inter_subset_left : U ∩ V ⊆ U) := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp, h₁₂]
  have H₁₃ : j₁₃ ≫ f₃ = f₁ ≫
      integralNestedChains (Set.inter_subset_right : U ∩ V ⊆ V) := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp, h₁₃]
  have H₂₄ : j₂₄ ≫ f₄ = f₂ ≫ integralSubspaceChains U := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp, h₂₄]
  have H₃₄ : j₃₄ ≫ f₄ = f₃ ≫ integralSubspaceChains V := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp, h₃₄]
  let m₂ := integralCoverMemberChains (integralBinaryCover U V) U true (fun _ h => h)
  let m₃ := integralCoverMemberChains (integralBinaryCover U V) V false (fun _ h => h)
  let ι := integralSmallChainInclusion (integralBinaryCover U V)
  let : Mono ι := integralSmallChainInclusion_mono (integralBinaryCover U V)
  have Hsmall : j₁₂ ≫ (f₂ ≫ m₂) = j₁₃ ≫ (f₃ ≫ m₃) := by
    apply (cancel_mono ι).mp
    simp only [Category.assoc, integralCoverMemberChains_inclusion, m₂, m₃, ι]
    rw [← Category.assoc, H₁₂, ← Category.assoc, H₁₃]
    simp only [Category.assoc, integralNestedChains_subspaceChains]
  let hp := SSet.chainComplex_subcomplex_isPushout integralCoefficient sq
  let t := hp.desc (f₂ ≫ m₂) (f₃ ≫ m₃) Hsmall
  have ht₂ : j₂₄ ≫ t = f₂ ≫ m₂ := hp.inl_desc _ _ Hsmall
  have ht₃ : j₃₄ ≫ t = f₃ ≫ m₃ := hp.inr_desc _ _ Hsmall
  let φ : hp.shortComplex ⟶ integralOpenChainSequence U V :=
    { τ₁ := f₁
      τ₂ := biprod.map f₂ f₃
      τ₃ := t
      comm₁₂ := by
        symm
        change biprod.lift j₁₂ (-j₁₃) ≫ biprod.map f₂ f₃ = f₁ ≫ integralOpenDifference U V
        apply biprod.hom_ext
        · simp only [integralOpenDifference, Category.assoc, biprod.map_fst,
            biprod.lift_fst_assoc]
          erw [biprod.lift_fst]
          exact H₁₂
        · simp only [integralOpenDifference, Category.assoc, biprod.map_snd,
            biprod.lift_snd_assoc]
          erw [biprod.lift_snd]
          simpa only [Preadditive.neg_comp, Preadditive.comp_neg] using
            congrArg Neg.neg H₁₃
      comm₂₃ := by
        symm
        change biprod.desc j₂₄ j₃₄ ≫ t = biprod.map f₂ f₃ ≫ integralOpenSum U V
        apply biprod.hom_ext'
        · simpa [integralOpenSum, Category.assoc, m₂] using ht₂
        · simpa [integralOpenSum, Category.assoc, m₃] using ht₃ }
  let : QuasiIso f₂ := hχ₂
  let : QuasiIso f₃ := hχ₃
  have ht : QuasiIso t := HomologySequence.quasiIso_τ₃ φ
    (SSet.chainComplex_subcomplex_shortExact integralCoefficient sq)
    (integralOpenChainSequence_shortExact U V) hχ₁ (quasiIso_biprod_map f₂ f₃)
  have hti : t ≫ ι = f₄ := by
    apply hp.hom_ext
    · change j₂₄ ≫ (t ≫ ι) = j₂₄ ≫ f₄
      rw [← Category.assoc, ht₂, H₂₄]
      simp only [Category.assoc, integralCoverMemberChains_inclusion, m₂, ι]
    · change j₃₄ ≫ (t ≫ ι) = j₃₄ ≫ f₄
      rw [← Category.assoc, ht₃, H₃₄]
      simp only [Category.assoc, integralCoverMemberChains_inclusion, m₃, ι]
  let : QuasiIso ι := integralOpenComparison_quasiIso U V hU hV hcover
  change QuasiIso f₄
  rw [← hti]
  infer_instance

end PoincareConjecture.Proofs.M59
