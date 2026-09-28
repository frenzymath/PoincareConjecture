import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Source
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_disjoint_contractible_retained_copy
    {X : Type*} (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (h₀ : closure B₀.outer.inside ⊆ interior J.space)
    (h₁ : closure B₁.outer.inside ⊆ interior J.space)
    (hdis : Disjoint (closure B₀.outer.inside) (closure B₁.outer.inside))
    (H : closure B₀.inner.inside ≃ₜ closure B₁.inner.inside) (hH : H.IsFinitePL)
    (f g : P2 → X)
    (hkeep0 : ∀ x : closure B₀.inner.inside, g (H x) = f x)
    (hkeep1 : ∀ x : closure B₁.inner.inside, g (H.symm x) = f x)
    (hout : EqOn g f (J.space \ (B₀.outer.inside ∪ B₁.outer.inside)))
    (hsingle : ∀ z ∈ A₀ ∪ A₁, ∀ w ∈ J.space, g w = g z → w = z) :
    let K := (closure B₀.inner.inside ∪ closure B₁.inner.inside) ∪
      (J.space \ (B₀.outer.inside ∪ B₁.outer.inside))
    ∃ j : K → P2,
      K ⊆ J.space ∧ Function.Injective j ∧ Continuous j ∧ range j = K ∧
      (∀ x, g (j x) = f x) ∧
      (∀ x, j x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space) ∧
      (∀ x : closure B₀.inner.inside, j ⟨x, Or.inl (Or.inl x.property)⟩ = (H x : P2)) ∧
      (∀ x : closure B₁.inner.inside, j ⟨x, Or.inl (Or.inr x.property)⟩ = (H.symm x : P2)) ∧
      (∀ x : {x : P2 // x ∈ J.space \ (B₀.outer.inside ∪ B₁.outer.inside)},
        j ⟨x, Or.inr x.property⟩ = x) ∧
      range j ∪ (A₀ ∪ A₁) = J.space ∧
      {v : P2 × P2 | v.1 ∈ J.space ∧ v.2 ∈ J.space ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (j v.1, j v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn g J.space = j '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      ∃ F : P2 → P2, FinitePiecewiseAffineOn F K ∧ ∀ x : K, F x = j x := by
  classical
  dsimp only
  let I₀ := closure B₀.inner.inside
  let I₁ := closure B₁.inner.inside
  let O := J.space \ (B₀.outer.inside ∪ B₁.outer.inside)
  let K := (I₀ ∪ I₁) ∪ O
  have hi₀ : I₀ ⊆ interior J.space := B₀.nested.trans (subset_closure.trans h₀)
  have hi₁ : I₁ ⊆ interior J.space := B₁.nested.trans (subset_closure.trans h₁)
  have hdisI : Disjoint I₀ I₁ := hdis.mono
    (B₀.nested.trans subset_closure) (B₁.nested.trans subset_closure)
  obtain ⟨hcover, _, _, _, _, _, hdisIO, _, _, _⟩ :=
    disjoint_contractible_source_partition B₀ B₁ (h₀.trans interior_subset)
      (h₁.trans interior_subset) hdis
  obtain ⟨KO, hKO, hKOs, _⟩ := exists_disjoint_contractible_exterior J hJ B₀ B₁ h₀ h₁ hdis
  have hclosedO : IsClosed O := by
    dsimp only [O]
    rw [← hKOs]
    exact (KO.isCompact_space_of_finite hKO).isClosed
  let j0 : I₀ → P2 := fun x ↦ H x
  let j1 : I₁ → P2 := fun x ↦ H.symm x
  let jA := joinSourceCopies hdisI j0 j1
  let jB : O → P2 := Subtype.val
  let j := joinSourceCopies hdisIO jA jB
  have hr0 : range j0 = I₁ := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (H y).property,
      fun hx ↦ ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩⟩
  have hr1 : range j1 = I₀ := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (H.symm y).property,
      fun hx ↦ ⟨H ⟨x, hx⟩, congrArg Subtype.val (H.symm_apply_apply _)⟩⟩
  have hrA : range jA = I₀ ∪ I₁ := by
    rw [joinSourceCopies_range, hr0, hr1, union_comm]
  have hrB : range jB = O := Subtype.range_val
  have hr : range j = K := by rw [joinSourceCopies_range, hrA, hrB]
  have hAi : Function.Injective jA := joinSourceCopies_injective hdisI
    (Subtype.val_injective.comp H.injective) (Subtype.val_injective.comp H.symm.injective)
    (by rw [hr0, hr1]; exact hdisI.symm)
  have hji : Function.Injective j := joinSourceCopies_injective hdisIO hAi
    Subtype.val_injective (by rwa [hrA, hrB])
  have hAc : Continuous jA := joinSourceCopies_continuous hdisI isClosed_closure
    isClosed_closure (continuous_subtype_val.comp H.continuous)
    (continuous_subtype_val.comp H.symm.continuous)
  have hjc : Continuous j := joinSourceCopies_continuous hdisIO
    (isClosed_closure.union isClosed_closure) hclosedO hAc continuous_subtype_val
  have hkeepA (x : (I₀ ∪ I₁ : Set P2)) : g (jA x) = f x :=
    joinSourceCopies_target hdisI hkeep0 hkeep1 x
  have hkeep (x : K) : g (j x) = f x :=
    joinSourceCopies_target hdisIO hkeepA (fun y ↦ hout y.property) x
  have hcov : range j ∪ (A₀ ∪ A₁) = J.space := by
    rw [hr]
    apply (Set.ext fun x ↦ ?_).trans hcover
    simp only [K, I₀, I₁, O, mem_union]
    tauto
  have hKsub : K ⊆ J.space := union_subset
    (union_subset (hi₀.trans interior_subset) (hi₁.trans interior_subset)) sdiff_subset
  have hbdA (x : (I₀ ∪ I₁ : Set P2)) : jA x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space :=
    iff_of_false
      (fun h ↦ disjoint_left.mp disjoint_interior_frontier
        (union_subset hi₀ hi₁ (hrA.subset (mem_range_self x))) h)
      (fun h ↦ disjoint_left.mp disjoint_interior_frontier (union_subset hi₀ hi₁ x.property) h)
  have hbd (x : K) : j x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space := by
    rcases x.property with hx | hx
    · rw [show j x = jA ⟨x, hx⟩ from joinSourceCopies_left hdisIO jA jB x hx]
      exact hbdA ⟨x, hx⟩
    · rw [show j x = jB ⟨x, hx⟩ from joinSourceCopies_right hdisIO jA jB x hx]
  refine ⟨j, hKsub, hji, hjc, hr, hkeep, hbd, ?_, ?_, ?_, hcov,
    retained_double_relation_eq j hji hcov hkeep hsingle,
    retained_double_locus_eq j hji hcov hkeep hsingle, ?_⟩
  · intro x
    exact (joinSourceCopies_left hdisIO jA jB _ (Or.inl x.property)).trans
      (joinSourceCopies_left hdisI j0 j1 _ x.property)
  · intro x
    exact (joinSourceCopies_left hdisIO jA jB _ (Or.inr x.property)).trans
      (joinSourceCopies_right hdisI j0 j1 _ x.property)
  · intro x
    exact joinSourceCopies_right hdisIO jA jB _ x.property
  · have hHs := hH.symm
    obtain ⟨F0, hF0, hF0val⟩ := hH
    obtain ⟨F1, hF1, hF1val⟩ := hHs
    have hid : FinitePiecewiseAffineOn (id : P2 → P2) O :=
      ⟨KO, hKO, hKOs, KO.affineOnFaces_affine (ContinuousAffineMap.id ℝ P2)⟩
    exact joinSourceCopies_exists_finitePL_extension hdisIO jA jB
      (joinSourceCopies_exists_finitePL_extension hdisI j0 j1
        ⟨F0, hF0, fun x ↦ (hF0val x).symm⟩ ⟨F1, hF1, fun x ↦ (hF1val x).symm⟩)
      ⟨id, hid, fun _ ↦ rfl⟩

end PoincareConjecture.M76.Dehn.Annuli
