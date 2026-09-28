import PoincareConjecture.Proofs.M83.LocalOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactOrientation











set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set
open scoped Topology unitInterval

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology


abbrev E3 := EuclideanSpace Real (Fin 3)



def euclideanLocalOrientation : LocalOrientation E3 := by
  exact ⟨exists_integralEuclideanOrientationData.choose,
    exists_integralEuclideanOrientationData.choose_spec.1,
    exists_integralEuclideanOrientationData.choose_spec.2⟩


def translation (a : E3) : C(E3, E3) := ⟨fun x => x + a, by fun_prop⟩



theorem translation_puncture (a : E3) :
    MapsTo (translation a) ({0}ᶜ : Set E3) ({a}ᶜ : Set E3) := by
  intro x hx h
  apply hx
  change x + a = a at h
  exact add_right_cancel (h.trans (zero_add a).symm)



theorem translation_preserves_orientation (O : LocalOrientation E3) (a : E3) :
    homologyMap (integralRelativeMap (translation a) (translation_puncture a)) 3
        (O.atPoint 0) = O.atPoint a := by
  let K : Set E3 := segment Real 0 a
  have hK : IsCompact K := by
    rw [show K = segment Real 0 a from rfl, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have h0K : (0 : E3) ∈ K := left_mem_segment Real 0 a
  have haK : a ∈ K := right_mem_segment Real 0 a
  let c := integralCompactSupportOrientation integralEuclideanSupportDetected
    O.atPoint ⟨K, hK⟩ O.locallyRepresented
  have hc (x : E3) (hx : x ∈ K) :
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3 c =
        O.atPoint x :=
    integralCompactSupportOrientation_spec integralEuclideanSupportDetected
      O.atPoint ⟨K, hK⟩ O.locallyRepresented x hx
  let H : ContinuousMap.Homotopy (ContinuousMap.id E3) (translation a) :=
    { toFun := fun z => z.2 + (z.1 : Real) • a
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [translation] }
  have hH : ∀ t : unitInterval, MapsTo (fun x => H (t, x)) Kᶜ ({a}ᶜ : Set E3) := by
    intro t x hx he
    apply hx
    have hxa : x = (1 - (t : Real)) • a := by
      have he' : x + (t : Real) • a = a := he
      rw [sub_smul, one_smul]
      exact eq_sub_iff_add_eq.mpr he'
    rw [hxa]
    exact ⟨(t : Real), 1 - (t : Real), t.property.1,
      sub_nonneg.mpr t.property.2, by ring, by simp⟩
  have hid : MapsTo (ContinuousMap.id E3) Kᶜ ({a}ᶜ : Set E3) := by
    intro x hx h
    change x = a at h
    exact hx (h.symm ▸ haK)
  have ht : MapsTo (translation a) Kᶜ ({a}ᶜ : Set E3) := by
    intro x hx
    exact translation_puncture a (fun h => hx (h.symm ▸ h0K))
  have hidChains : integralRelativeMap (ContinuousMap.id E3) hid =
      integralSupportRestriction (singleton_subset_iff.mpr haK) := by
    apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
    rw [integralRelativeMap_projection, integralSupportRestriction_projection]
    change integralChainsFunctor.map (𝟙 (TopCat.of E3)) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have htChains : integralRelativeMap (translation a) ht =
      integralSupportRestriction (singleton_subset_iff.mpr h0K) ≫
        integralRelativeMap (translation a) (translation_puncture a) := by
    apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
    rw [integralRelativeMap_projection, ← Category.assoc,
      integralSupportRestriction_projection, integralRelativeMap_projection]
  have hh := congrArg (fun f => f c)
    (relativeHomologyMap_eq_of_homotopy H hid ht hH 3)
  rw [hidChains, htChains, homologyMap_comp, ModuleCat.comp_apply] at hh
  change integralSupportHomologyRestriction (singleton_subset_iff.mpr haK) 3 c =
    homologyMap (integralRelativeMap (translation a) (translation_puncture a)) 3
      (integralSupportHomologyRestriction (singleton_subset_iff.mpr h0K) 3 c) at hh
  rw [hc a haK, hc 0 h0K] at hh
  exact hh.symm

end PoincareConjecture.Proofs.M83
