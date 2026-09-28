import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedProperness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_nested_contractible_retained_copy
    {X : Type*} (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (hcontract : closure B₀.outer.inside ⊆ interior J.space)
    (hnest : closure B₁.outer.inside ⊆ B₀.inner.inside)
    (H : closure B₁.inner.inside ≃ₜ closure B₀.inner.inside) (hH : H.IsFinitePL)
    (f g : P2 → X) (hkeep : ∀ x : closure B₁.inner.inside, g (H x) = f x)
    (hout : EqOn g f (J.space \ B₀.outer.inside))
    (hsingle : ∀ z ∈ A₀, ∀ w ∈ J.space, g w = g z → w = z) :
    let K := closure B₁.inner.inside ∪ (J.space \ B₀.outer.inside)
    ∃ copy : K → P2,
      K ⊆ J.space ∧ Function.Injective copy ∧ Continuous copy ∧
      (∀ x, copy x ∈ J.space) ∧ (∀ x, g (copy x) = f x) ∧
      (∀ x, copy x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space) ∧
      (∀ x : closure B₁.inner.inside, copy ⟨x, Or.inl x.property⟩ = (H x : P2)) ∧
      (∀ x : {x : P2 // x ∈ J.space \ B₀.outer.inside},
        copy ⟨x, Or.inr x.property⟩ = x) ∧
      range copy ∪ A₀ = J.space ∧
      {v : P2 × P2 | v.1 ∈ J.space ∧ v.2 ∈ J.space ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (copy v.1, copy v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn g J.space = copy '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      ∃ F : P2 → P2, FinitePiecewiseAffineOn F K ∧ ∀ x : K, F x = copy x := by
  classical
  dsimp only
  obtain ⟨_, _, _, O, _, _, _, _, _, _, _, _, hO, hOs,
    hcover, _, _, hIO, hQS, _⟩ := exists_nested_contractible_source J hJ B₀ B₁ hcontract hnest
  have hIint : closure B₀.inner.inside ⊆ interior J.space :=
    B₀.nested.trans (subset_closure.trans hcontract)
  have hQI : closure B₁.inner.inside ⊆ B₀.inner.inside :=
    B₁.nested.trans (subset_closure.trans hnest)
  have hQint : closure B₁.inner.inside ⊆ interior J.space :=
    hQI.trans (subset_closure.trans hIint)
  have hIO' : Disjoint (closure B₀.inner.inside) (J.space \ B₀.outer.inside) := by
    simpa only [hOs] using hIO
  have hQO : Disjoint (closure B₁.inner.inside) (J.space \ B₀.outer.inside) :=
    hIO'.mono_left (hQI.trans subset_closure)
  have hclosedO : IsClosed (J.space \ B₀.outer.inside) :=
    (J.isCompact_space_of_finite hJ).isClosed.sdiff
      (B₀.outer.isOpen_inside B₀.outer_simplicial B₀.outer_injective)
  let jA : closure B₁.inner.inside → P2 := fun x ↦ H x
  let jB : {x : P2 // x ∈ J.space \ B₀.outer.inside} → P2 := Subtype.val
  let copy := joinSourceCopies hQO jA jB
  have hrA : range jA = closure B₀.inner.inside := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (H y).property
    · intro hx
      exact ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩
  have hrB : range jB = J.space \ B₀.outer.inside := Subtype.range_val
  have hr : range copy = closure B₀.inner.inside ∪ (J.space \ B₀.outer.inside) := by
    rw [joinSourceCopies_range, hrA, hrB]
  have hci : Function.Injective copy := joinSourceCopies_injective hQO
    (Subtype.val_injective.comp H.injective) Subtype.val_injective (by rwa [hrA, hrB])
  have hcc : Continuous copy := joinSourceCopies_continuous hQO isClosed_closure hclosedO
    (continuous_subtype_val.comp H.continuous) continuous_subtype_val
  have hcov : range copy ∪ A₀ = J.space := by
    rw [hr]
    simpa only [hOs, union_right_comm] using hcover
  have hkeep' (x : {x : P2 // x ∈ closure B₁.inner.inside ∪
      (J.space \ B₀.outer.inside)}) :
      g (copy x) = f x := joinSourceCopies_target hQO hkeep (fun y ↦ hout y.property) x
  have hboundary (x : {x : P2 // x ∈ closure B₁.inner.inside ∪
      (J.space \ B₀.outer.inside)}) :
      copy x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space := by
    rcases x.property with hx | hx
    · rw [show copy x = jA ⟨x, hx⟩ from joinSourceCopies_left hQO jA jB x hx]
      exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hIint (H ⟨x, hx⟩).property) h)
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hQint hx) h)
    · rw [show copy x = jB ⟨x, hx⟩ from joinSourceCopies_right hQO jA jB x hx]
  refine ⟨copy, union_subset hQS sdiff_subset, hci, hcc,
    fun x ↦ hcov.subset (Or.inl (mem_range_self x)), hkeep', hboundary,
    fun x ↦ joinSourceCopies_left hQO jA jB _ x.property,
    fun x ↦ joinSourceCopies_right hQO jA jB _ x.property,
    hcov, retained_double_relation_eq copy hci hcov hkeep' hsingle,
    retained_double_locus_eq copy hci hcov hkeep' hsingle, ?_⟩
  obtain ⟨F, hF, hFval⟩ := hH
  have hid : FinitePiecewiseAffineOn (id : P2 → P2) (J.space \ B₀.outer.inside) :=
    ⟨O, hO, hOs, O.affineOnFaces_affine (ContinuousAffineMap.id ℝ P2)⟩
  exact joinSourceCopies_exists_finitePL_extension hQO jA jB
    ⟨F, hF, fun x ↦ (hFval x).symm⟩ ⟨id, hid, fun _ ↦ rfl⟩

end PoincareConjecture.M76.Dehn.Annuli
