import PoincareLib.Topology.Manifold.EmbeddedSphere.Parity.IntegerCoordinates
import PoincareLib.Topology.Manifold.EmbeddedSphere.Homology.TwoPointSupport
import PoincareLib.Topology.Manifold.EmbeddedSphere.Homology.TwoPuncture
import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.Triple
import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralSupportLocalization

/-!
# Parity of the actual local model boundary

Equal intrinsic parities at the two punctures force the actual triple
boundary to be even. The canonical maps are identified by composition
of relative restrictions; compact-convex support restriction supplies
the diagonal isomorphisms. Local cyclicity is an explicit input, with
no compatibility between its two choices of sign. Source: M53 derivation
09, Hatcher, pp. 117-118 and 233-235, for the separation repair of
Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

/-- Equal parities of the two actual point restrictions imply an even
triple boundary in the plane-plus-convex-exterior model. The supplied
local integer coordinates need no compatible orientations. Source: M53
derivation 09 and Hatcher, pp. 117-118 and 233-235. -/
theorem even_planeExterior_tripleBoundary_of_point_parity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set (E × ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (c : ℝ) (hc : 0 < c) (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) (n : Nat)
    (ep : integralSupportHomology ({((0 : E), c)} : Set (E × ℝ)) (n + 1) ≃+ ℤ)
    (em : integralSupportHomology ({((0 : E), -c)} : Set (E × ℝ)) (n + 1) ≃+ ℤ)
    (a : integralRelativeHomology ({y : E × ℝ | y.2 = 0} ∪ Kᶜ) (n + 1))
    (ha : let b := homologyMap (integralRelativeRestriction
          (planeExterior_subset_twoPuncture K c hc hp hm)) (n + 1) a
      Even (integralSupportHomologyRestriction
        (Set.subset_union_left : ({((0 : E), c)} : Set (E × ℝ)) ⊆ {(0, c)} ∪ {(0, -c)})
          (n + 1) b) ↔
      Even (integralSupportHomologyRestriction
        (Set.subset_union_right : ({((0 : E), -c)} : Set (E × ℝ)) ⊆ {(0, c)} ∪ {(0, -c)})
          (n + 1) b)) :
    Even (integralTripleBoundary ({y : E × ℝ | y.2 = 0} ∪ Kᶜ) Kᶜ
      Set.subset_union_right n a) := by
  let A : Set (E × ℝ) := {y | y.2 = 0} ∪ Kᶜ
  let f := homologyMap (integralRelativeRestriction
    (Set.subset_union_right : Kᶜ ⊆ A)) (n + 1)
  let F := homologyMap (integralRelativeRestriction
    (planeExterior_subset_twoPuncture K c hc hp hm)) (n + 1)
  let rp := integralSupportHomologyRestriction
    (Set.subset_union_left : ({((0 : E), c)} : Set (E × ℝ)) ⊆ {(0, c)} ∪ {(0, -c)}) (n + 1)
  let rm := integralSupportHomologyRestriction
    (Set.subset_union_right : ({((0 : E), -c)} : Set (E × ℝ)) ⊆ {(0, c)} ∪ {(0, -c)}) (n + 1)
  let kp := integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hp) (n + 1)
  let km := integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hm) (n + 1)
  let δ := integralTripleBoundary A Kᶜ Set.subset_union_right n
  let p := ep.toAddMonoidHom.comp (F ≫ rp).hom.toAddMonoidHom
  let q := em.toAddMonoidHom.comp (F ≫ rm).hom.toAddMonoidHom
  have hxy : ((0 : E), c) ≠ (0, -c) := by
    intro h
    have he := congrArg Prod.snd h
    linarith
  let : IsIso F := planeExterior_twoPuncture_homology_isIso K hK hconv c hc hp hm (n + 1)
  have hpair : Function.Bijective (fun z => (p z, q z)) :=
    (ep.prodCongr em).bijective.comp
      ((integralSupportHomology_twoPoint_bijective (0, c) (0, -c) hxy (n + 1)).comp
        (asIso F).toLinearEquiv.bijective)
  have hkp : f ≫ F ≫ rp = kp := by
    change homologyMap (integralRelativeRestriction _) (n + 1) ≫
      homologyMap (integralRelativeRestriction _) (n + 1) ≫
      homologyMap (integralRelativeRestriction _) (n + 1) =
      homologyMap (integralRelativeRestriction _) (n + 1)
    simp only [← homologyMap_comp, integralRelativeRestriction_comp]
  have hkm : f ≫ F ≫ rm = km := by
    change homologyMap (integralRelativeRestriction _) (n + 1) ≫
      homologyMap (integralRelativeRestriction _) (n + 1) ≫
      homologyMap (integralRelativeRestriction _) (n + 1) =
      homologyMap (integralRelativeRestriction _) (n + 1)
    simp only [← homologyMap_comp, integralRelativeRestriction_comp]
  let : IsIso kp := integralCompactConvexSupportRestriction_homology_isIso
    K hK hconv (0, c) hp (n + 1)
  let : IsIso km := integralCompactConvexSupportRestriction_homology_isIso
    K hK hconv (0, -c) hm (n + 1)
  have hpf : p.comp f.hom.toAddMonoidHom = ep.toAddMonoidHom.comp kp.hom.toAddMonoidHom := by
    ext d
    exact congrArg ep (congrArg (fun g => g d) hkp)
  have hqf : q.comp f.hom.toAddMonoidHom = em.toAddMonoidHom.comp km.hom.toAddMonoidHom := by
    ext d
    exact congrArg em (congrArg (fun g => g d) hkm)
  have hpf_bij : Function.Bijective (p.comp f.hom.toAddMonoidHom) := by
    rw [hpf]
    exact ep.bijective.comp (asIso kp).toLinearEquiv.bijective
  have hqf_bij : Function.Bijective (q.comp f.hom.toAddMonoidHom) := by
    rw [hqf]
    exact em.bijective.comp (asIso km).toLinearEquiv.bijective
  have hfδ : f ≫ δ = 0 :=
    (integralNestedRelativePairSequence_shortExact Kᶜ A Set.subset_union_right).comp_δ
      (n + 1) n rfl
  have hδf : δ.hom.toAddMonoidHom.comp f.hom.toAddMonoidHom = 0 := by
    ext d
    exact congrArg (fun g => g d) hfδ
  have hpar : Even (p a) ↔ Even (q a) :=
    ((ep.even_apply_iff _).trans ha).trans (em.even_apply_iff _).symm
  exact AddMonoidHom.even_apply_of_integer_coordinates f.hom.toAddMonoidHom p q
    δ.hom.toAddMonoidHom hpair hpf_bij hqf_bij hδf a hpar

end PoincareMT.Topology.EmbeddedSphere
