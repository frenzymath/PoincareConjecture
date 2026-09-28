import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff









set_option autoImplicit false

open Set

namespace Continuous

variable {X : Type*} [TopologicalSpace X] [T2Space X] {K : Set X} {f : X → X}


theorem isClosedMap_of_eqOn_compl_isCompact (hf : Continuous f) (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → f x = x) : IsClosedMap f := by
  intro F hF
  have hfixed : IsClosed {x | f x = x} := isClosed_eq hf continuous_id
  have himage : f '' F = f '' (F ∩ K) ∪ (F ∩ {x | f x = x}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨x, ⟨hx, hxK⟩, rfl⟩
      · right
        rw [hfix x hxK]
        exact ⟨hx, hfix x hxK⟩
    · rintro (⟨x, ⟨hx, _⟩, rfl⟩ | ⟨hy, hfy⟩)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, hfy⟩
  rw [himage]
  exact ((hK.inter_left hF).image hf).isClosed.union (hF.inter hfixed)



theorem isHomeomorph_of_bijective_eqOn_compl_isCompact (hf : Continuous f)
    (hbij : Function.Bijective f) (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → f x = x) : IsHomeomorph f :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨hf, hf.isClosedMap_of_eqOn_compl_isCompact hK hfix, hbij⟩

end Continuous

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X] {U K : Set X}



theorem image_connectedComponent_eq_of_eqOn_compl (e : X ≃ₜ X)
    (hU : IsPreconnected U) (hfix : ∀ x, x ∉ U → e x = x) (x : X) :
    e '' connectedComponent x = connectedComponent x := by
  have hcomponent : connectedComponent (e x) = connectedComponent x := by
    by_cases hx : x ∈ U
    · have hex : e x ∈ U := by
        by_contra he
        have heq : e x = x := e.injective (hfix (e x) he)
        exact he (heq.symm ▸ hx)
      exact (connectedComponent_eq (hU.subset_connectedComponent hx hex)).symm
    · rw [hfix x hx]
  have hi := e.image_connectedComponentIn (s := univ) (x := x) (mem_univ x)
  simpa only [image_univ, e.surjective.range_eq, connectedComponentIn_univ, hcomponent] using hi

private noncomputable def extendEquiv (e : U ≃ₜ U) : Equiv.Perm X := by
  classical
  exact Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U)

private theorem extendEquiv_apply (e : U ≃ₜ U) (x : U) :
    extendEquiv e x = (e x : X) := by
  classical
  exact Equiv.Perm.extendDomain_apply_image e.toEquiv (Equiv.refl U) x

private theorem extendEquiv_apply_of_notMem (e : U ≃ₜ U) {x : X} (hx : x ∉ U) :
    extendEquiv e x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype e.toEquiv (Equiv.refl U) hx

private theorem extendEquiv_fixed (e : U ≃ₜ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) {x : X} (hx : x ∉ K) :
    extendEquiv e x = x := by
  by_cases hU : x ∈ U
  · rw [show x = ((⟨x, hU⟩ : U) : X) from rfl, extendEquiv_apply, hfix _ hx]
  · exact extendEquiv_apply_of_notMem e hU

private theorem continuous_extendEquiv (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) :
    Continuous (extendEquiv e) := by
  have hinside : ContinuousOn (extendEquiv e) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : U.domRestrict (extendEquiv e) = fun x : U => (e x : X) := by
      funext x
      exact extendEquiv_apply e x
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have houtside : ContinuousOn (extendEquiv e) Kᶜ := by
    apply continuous_id.continuousOn.congr
    intro x hx
    exact extendEquiv_fixed e hfix hx
  have hcover : U ∪ Kᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    exact or_iff_not_imp_right.mpr (fun hx => hKU (not_not.mp hx))
  rw [← continuousOn_univ, ← hcover]
  exact hinside.union_of_isOpen houtside hU hK.isOpen_compl



noncomputable def extendOfIsClosed (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) : X ≃ₜ X where
  toEquiv := extendEquiv e
  continuous_toFun := continuous_extendEquiv e hU hK hKU hfix
  continuous_invFun := by
    change Continuous (extendEquiv e.symm)
    apply continuous_extendEquiv e.symm hU hK hKU
    intro x hx
    apply e.injective
    rw [e.apply_symm_apply, hfix x hx]

@[simp] theorem extendOfIsClosed_apply (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) (x : U) :
    e.extendOfIsClosed hU hK hKU hfix x = (e x : X) :=
  extendEquiv_apply e x


theorem extendOfIsClosed_apply_of_notMem (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) {x : X} (hx : x ∉ K) :
    e.extendOfIsClosed hU hK hKU hfix x = x :=
  extendEquiv_fixed e hfix hx


theorem extendOfIsClosed_image (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) (S : Set U) :
    e.extendOfIsClosed hU hK hKU hfix '' (Subtype.val '' S) =
      Subtype.val '' (e '' S) := by
  rw [← image_comp, ← image_comp]
  congr 1
  funext x
  exact extendOfIsClosed_apply e hU hK hKU hfix x



noncomputable def extendOfIsCompact [T2Space X] (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) : X ≃ₜ X :=
  e.extendOfIsClosed hU hK.isClosed hKU hfix

@[simp] theorem extendOfIsCompact_apply [T2Space X] (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) (x : U) :
    e.extendOfIsCompact hU hK hKU hfix x = (e x : X) :=
  extendOfIsClosed_apply e hU hK.isClosed hKU hfix x

theorem extendOfIsCompact_apply_of_notMem [T2Space X] (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) {x : X} (hx : x ∉ K) :
    e.extendOfIsCompact hU hK hKU hfix x = x :=
  extendOfIsClosed_apply_of_notMem e hU hK.isClosed hKU hfix hx

theorem extendOfIsCompact_image [T2Space X] (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x) (S : Set U) :
    e.extendOfIsCompact hU hK hKU hfix '' (Subtype.val '' S) =
      Subtype.val '' (e '' S) :=
  extendOfIsClosed_image e hU hK.isClosed hKU hfix S



theorem extendOfIsCompact_image_connectedComponent [T2Space X] (e : U ≃ₜ U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : X) ∉ K → e x = x)
    (hconn : IsPreconnected U) (x : X) :
    e.extendOfIsCompact hU hK hKU hfix '' connectedComponent x = connectedComponent x := by
  apply image_connectedComponent_eq_of_eqOn_compl _ hconn
  intro y hy
  exact extendOfIsCompact_apply_of_notMem e hU hK hKU hfix (fun hyK => hy (hKU hyK))

end Homeomorph
