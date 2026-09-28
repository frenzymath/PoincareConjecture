import PoincareConjecture.Proofs.M02.Topology.IntegralLocalHomology
import PoincareConjecture.Proofs.M02.Topology.IntegralThreeManifoldTop

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M40

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralToRelativeHomology_map_naturality
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (n : Nat) :
    integralToRelativeHomology A n ≫ homologyMap (integralRelativeMap f hf) n =
      homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) n ≫
        integralToRelativeHomology B n := by
  simpa only [integralToRelativeHomology, homologyMap_comp] using
    congrArg (fun k => homologyMap k n) (integralRelativeMap_projection f hf)

theorem integralLocalHomologyMap_isIso
    [T1Space X] [T1Space Y] (f : C(X, Y)) (x : X)
    (e : OpenPartialHomeomorph X Y) (hx : x ∈ e.source)
    (he : EqOn f e e.source)
    (hf : MapsTo f ({x}ᶜ : Set X) ({f x}ᶜ : Set Y)) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap f hf) n) := by
  let A : Set e.source := (Subtype.val : e.source → X) ⁻¹' ({x}ᶜ : Set X)
  let B : Set e.target := (Subtype.val : e.target → Y) ⁻¹' ({f x}ᶜ : Set Y)
  have hpair (z : e.source) : z ∈ A ↔ e.toHomeomorphSourceTarget z ∈ B := by
    change z.val ≠ x ↔ e z.val ≠ f x
    rw [he hx]
    constructor
    · intro hz hzx
      exact hz (e.injOn z.property hx hzx)
    · intro hz hzx
      exact hz (congrArg e hzx)
  let E := integralRelativeHomeomorphIso e.toHomeomorphSourceTarget A B hpair
  let iX := integralLocalRelativeMap x e.source
  let iY := integralLocalRelativeMap (f x) e.target
  let jX : C(e.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let jY : C(e.target, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hX : integralRelativeProjection A ≫ iX =
      integralChainsFunctor.map (TopCat.ofHom jX) ≫
        integralRelativeProjection ({x}ᶜ : Set X) :=
    integralRelativeMap_projection jX (fun _ hz => hz)
  have hY : integralRelativeProjection B ≫ iY =
      integralChainsFunctor.map (TopCat.ofHom jY) ≫
        integralRelativeProjection ({f x}ᶜ : Set Y) :=
    integralRelativeMap_projection jY (fun _ hz => hz)
  have hE : integralRelativeProjection A ≫ E.hom =
      integralChainsFunctor.map
        (TopCat.ofHom (e.toHomeomorphSourceTarget : C(e.source, e.target))) ≫
          integralRelativeProjection B :=
    integralRelativeHomeomorphIso_projection _ _ _ _
  have hmaps : TopCat.ofHom jX ≫ TopCat.ofHom f =
      TopCat.ofHom (e.toHomeomorphSourceTarget : C(e.source, e.target)) ≫
        TopCat.ofHom jY := by
    ext z
    exact he z.property
  have hsquare : iX ≫ integralRelativeMap f hf = E.hom ≫ iY := by
    apply (cancel_epi (integralRelativeProjection A)).mp
    calc
      integralRelativeProjection A ≫ (iX ≫ integralRelativeMap f hf) =
          integralChainsFunctor.map (TopCat.ofHom jX) ≫
            integralChainsFunctor.map (TopCat.ofHom f) ≫
              integralRelativeProjection ({f x}ᶜ : Set Y) := by
        rw [← Category.assoc, hX, Category.assoc, integralRelativeMap_projection]
      _ = integralChainsFunctor.map
          (TopCat.ofHom (e.toHomeomorphSourceTarget : C(e.source, e.target))) ≫
            integralChainsFunctor.map (TopCat.ofHom jY) ≫
              integralRelativeProjection ({f x}ᶜ : Set Y) := by
        rw [← Category.assoc, ← integralChainsFunctor.map_comp, hmaps,
          integralChainsFunctor.map_comp, Category.assoc]
      _ = integralRelativeProjection A ≫ (E.hom ≫ iY) := by
        rw [← Category.assoc (integralRelativeProjection A), hE,
          Category.assoc, hY]
  let : IsIso (homologyMap iX n) :=
    integral_local_relative_excision x e.source e.open_source hx n
  have hy : f x ∈ e.target := by
    rw [he hx]
    exact e.map_source hx
  let : IsIso (homologyMap iY n) :=
    integral_local_relative_excision (f x) e.target e.open_target hy n
  have hhom := congrArg (fun k => homologyMap k n) hsquare
  rw [homologyMap_comp, homologyMap_comp] at hhom
  apply (isIso_comp_left_iff (homologyMap iX n) _).mp
  rw [hhom]
  infer_instance

theorem integralLocalHomologyMap_isIso_of_unique_preimage
    [T1Space X] [T1Space Y] (f : C(X, Y)) (x : X)
    (e : OpenPartialHomeomorph X Y) (hx : x ∈ e.source)
    (he : EqOn f e e.source)
    (hunique : ∀ z : X, f z = f x → z = x) (n : Nat) :
    IsIso (homologyMap
      (integralRelativeMap f (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
        (fun z hz hzx => hz (hunique z hzx))) n) :=
  integralLocalHomologyMap_isIso f x e hx he _ n

theorem integralSupportHomologyRestriction_point_bijective
    [T2Space X] [RegularSpace X] [CompactSpace X] [PreconnectedSpace X]
    (n : Nat) (x : X)
    (hD : ∀ K : Set X, IsCompact K → IntegralSupportDetected K n)
    (omega : ∀ z : X, integralSupportHomology ({z} : Set X) n)
    (basis : ∀ z : X, Int ≃ₗ[Int] integralSupportHomology ({z} : Set X) n)
    (hbasis : ∀ z : X, basis z 1 = omega z)
    (hlocal : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧
      ∃ b : integralSupportHomology U n,
        ∀ w : X, ∀ hw : w ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hw) n b = omega w) :
    Function.Bijective
      (integralSupportHomologyRestriction (subset_univ ({x} : Set X)) n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    apply hD univ isCompact_univ
    intro z _
    apply (basis z).symm.injective
    rw [map_zero]
    have hc := (integralSupportHomology_coefficient_locallyConstant
      n omega basis hbasis hlocal a).apply_eq_of_preconnectedSpace z x
    exact hc.trans (by rw [ha, map_zero])
  · obtain ⟨a, ha, _⟩ := exists_unique_integralSupportHomology_compact_gluing
      n hD omega univ isCompact_univ (fun z _ => hlocal z)
    intro b
    refine ⟨(basis x).symm b • a, ?_⟩
    rw [map_zsmul, ha x (mem_univ x), ← hbasis x, ← map_zsmul]
    simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using
      (basis x).apply_symm_apply b

theorem integralThirdHomology_toLocal_isIso
    [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) X]
    [SimplyConnectedSpace X] (x : X) :
    IsIso (integralToRelativeHomology ({x}ᶜ : Set X) 3) := by
  classical
  obtain ⟨omega, hgen, hlocal⟩ := exists_integralThreeLocallyRepresentedGenerators x
  choose basis hbasis using hgen
  have hbij := integralSupportHomologyRestriction_point_bijective 3 x
    (fun K hK => (integralThreeManifoldCompactSupport K hK).2)
    omega basis hbasis hlocal
  let r := integralSupportHomologyRestriction (subset_univ ({x} : Set X)) 3
  let : IsIso r := (ConcreteCategory.isIso_iff_bijective r).mpr hbij
  have hproj : IsIso (integralToRelativeHomology ((univ : Set X)ᶜ) 3) := by
    rw [compl_univ]
    let := integralRelativeProjection_empty_isIso (X := X)
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) 3).map _)
    infer_instance
  let := hproj
  have hfactor : integralToRelativeHomology ((univ : Set X)ᶜ) 3 ≫ r =
      integralToRelativeHomology ({x}ᶜ : Set X) 3 := by
    change homologyMap (integralRelativeProjection _) 3 ≫
      homologyMap (integralSupportRestriction _) 3 = _
    rw [← homologyMap_comp, integralSupportRestriction_projection]
  rw [← hfactor]
  infer_instance

theorem integralThirdHomologyMap_bijective_of_unique_preimage
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) X]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X) (e : OpenPartialHomeomorph X Y)
    (hx : x ∈ e.source) (he : EqOn f e e.source)
    (hunique : ∀ z : X, f z = f x → z = x) :
    Function.Bijective
      (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 3) := by
  let hf : MapsTo f ({x}ᶜ : Set X) ({f x}ᶜ : Set Y) :=
    fun z hz hzx => hz (hunique z hzx)
  let : IsIso (homologyMap (integralRelativeMap f hf) 3) :=
    integralLocalHomologyMap_isIso f x e hx he hf 3
  let : IsIso (integralToRelativeHomology ({x}ᶜ : Set X) 3) :=
    integralThirdHomology_toLocal_isIso x
  let : IsIso (integralToRelativeHomology ({f x}ᶜ : Set Y) 3) :=
    integralThirdHomology_toLocal_isIso (f x)
  have hsquare := integralToRelativeHomology_map_naturality f hf 3
  have hcomp : IsIso
      (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 3 ≫
        integralToRelativeHomology ({f x}ᶜ : Set Y) 3) := by
    rw [← hsquare]
    infer_instance
  let : IsIso (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 3) :=
    (isIso_comp_right_iff _ (integralToRelativeHomology ({f x}ᶜ : Set Y) 3)).mp hcomp
  exact ConcreteCategory.bijective_of_isIso _

end PoincareConjecture.Proofs.M40
