import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FiniteComponentHomologyChains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FiniteComplexHomologyDomain
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Topology CategoryTheory Limits HomologicalComplex
open scoped DirectSum BigOperators Classical

universe u v

namespace PoincareConjecture.M76.FiniteComponentHomology

variable {X V : Type u} [TopologicalSpace X] [T2Space X] [Finite V]
  (Q : Set X) (D : V → Set X) (hD : ∀ v, IsCompact (D v))
  (hdis : Pairwise fun v w => Disjoint (D v) (D w)) (hcover : (⋃ v, D v) = Q)

def componentInclusion (v : V) : C(D v, Q) :=
  ⟨fun x => ⟨x, hcover ▸ mem_iUnion.mpr ⟨v, x.property⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

def componentsHomeomorph : (Σ v, D v) ≃ₜ Q := by
  let : ∀ v, CompactSpace (D v) := fun v => isCompact_iff_compactSpace.mp (hD v)
  let f : (Σ v, D v) → Q := fun z => componentInclusion Q D hcover z.1 z.2
  have hf : Continuous f := continuous_sigma (fun v => (componentInclusion Q D hcover v).continuous)
  have hinj : Function.Injective f := by
    rintro ⟨v, x⟩ ⟨w, y⟩ he
    have hxy : (x : X) = y := congrArg Subtype.val he
    have hvw : v = w := by
      by_contra hn
      exact disjoint_left.mp (hdis hn) x.property (hxy ▸ y.property)
    subst w
    exact congrArg (Sigma.mk v) (Subtype.ext hxy)
  have hsurj : Function.Surjective f := by
    intro x
    have hx : (x : X) ∈ ⋃ v, D v := by rw [hcover]; exact x.property
    obtain ⟨v, hv⟩ := mem_iUnion.mp hx
    exact ⟨⟨v, ⟨x, hv⟩⟩, rfl⟩
  exact (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hinj, hsurj⟩).homeomorph f

def componentsHomologyIso (n : ℕ) :
    ModuleCat.of (ZMod 2) (⨁ v, ModTwoMayerVietoris.homology (D v) n) ≅
      ModTwoMayerVietoris.homology Q n :=
  (ModuleCat.coprodIsoDirectSum (fun v => ModTwoMayerVietoris.homology (D v) n)).symm ≪≫
    homologySigmaIso (fun v => D v) n ≪≫
    (homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) n).mapIso
      (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
        ModTwoMayerVietoris.coefficient).mapIso
          (TopCat.toSSet.mapIso
            (TopCat.isoOfHomeo (X := TopCat.of (Σ v, D v)) (Y := TopCat.of Q)
              (componentsHomeomorph Q D hD hdis hcover))))

@[reassoc]
theorem componentsHomologyIso_inclusion (n : ℕ) (v : V) :
    ModuleCat.ofHom (DirectSum.lof (ZMod 2) V
      (fun v => ModTwoMayerVietoris.homology (D v) n) v) ≫
        (componentsHomologyIso Q D hD hdis hcover n).hom =
      ModTwoMayerVietoris.homologyMapOf (componentInclusion Q D hcover v) n := by
  dsimp only [componentsHomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ModuleCat.lof_coprodIsoDirectSum_inv,
    homologySigmaIso_inclusion_assoc]
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n
  rw [← homologyMap_comp]
  congr 1
  let F := (SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
    ModTwoMayerVietoris.coefficient
  change F.map _ ≫ F.map _ = F.map _
  rw [← CategoryTheory.Functor.map_comp]
  congr 1

include hD hdis hcover in
theorem finrank_components [Fintype V] (n : ℕ)
    [∀ v, Module.Finite (ZMod 2) (ModTwoMayerVietoris.homology (D v) n)] :
    Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology Q n) =
      ∑ v, Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology (D v) n) := by
  classical
  rw [← (componentsHomologyIso Q D hD hdis hcover n).toLinearEquiv.finrank_eq,
    Module.finrank_directSum]

end PoincareConjecture.M76.FiniteComponentHomology

namespace PoincareConjecture.M76

theorem PLDomain.finrank_disjoint_components
    {X V : Type u} {ι : Type v} [TopologicalSpace X] [T2Space X] [Fintype V]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (Q : Set X) (D : V → Set X) (hD : ∀ v, IsCompact (D v))
    (hPL : ∀ v, PLDomain e (D v))
    (hdis : Pairwise fun v w => Disjoint (D v) (D w)) (hcover : (⋃ v, D v) = Q)
    (n : ℕ) :
    Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology Q n) =
      ∑ v, Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology (D v) n) := by
  let : ∀ v, Module.Finite (ZMod 2) (ModTwoMayerVietoris.homology (D v) n) :=
    fun v => (hPL v).finite_modTwo_homology (hD v) n
  exact FiniteComponentHomology.finrank_components Q D hD hdis hcover n

end PoincareConjecture.M76
