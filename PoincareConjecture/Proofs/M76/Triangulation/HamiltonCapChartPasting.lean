import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {s u : Set X} {t v : Set Y}

private theorem closed_piece_homeomorph
    (hs : IsClosed ((Subtype.val : (s ∪ u : Set X) → X) ⁻¹' s))
    (hu : IsClosed ((Subtype.val : (s ∪ u : Set X) → X) ⁻¹' u))
    (ht : IsClosed ((Subtype.val : (t ∪ v : Set Y) → Y) ⁻¹' t))
    (hv : IsClosed ((Subtype.val : (t ∪ v : Set Y) → Y) ⁻¹' v))
    (e : s ≃ₜ t) (f : u ≃ₜ v)
    (hoverlap : ∀ x : s, (x : X) ∈ u ↔ (e x : Y) ∈ v)
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x, hxs⟩ : Y) = (f ⟨x, hxu⟩ : Y)) :
    ∃ H : (s ∪ u : Set X) ≃ₜ (t ∪ v : Set Y),
      (∀ x : s, (H ⟨x, Or.inl x.property⟩ : Y) = e x) ∧
      (∀ x : u, (H ⟨x, Or.inr x.property⟩ : Y) = f x) := by
  classical
  let F : (s ∪ u : Set X) → (t ∪ v : Set Y) := fun x =>
    if hx : (x : X) ∈ s then ⟨e ⟨x, hx⟩, Or.inl (e ⟨x, hx⟩).property⟩
    else ⟨f ⟨x, x.property.resolve_left hx⟩,
      Or.inr (f ⟨x, x.property.resolve_left hx⟩).property⟩
  have hFs (x : s) : F ⟨x, Or.inl x.property⟩ =
      ⟨e x, Or.inl (e x).property⟩ := by
    simp only [F, dif_pos x.property]
  have hFu (x : u) : F ⟨x, Or.inr x.property⟩ =
      ⟨f x, Or.inr (f x).property⟩ := by
    by_cases hx : (x : X) ∈ s
    · apply Subtype.ext
      simpa only [F, dif_pos hx] using hagree x hx x.property
    · simp only [F, dif_neg hx]
  let S : Set (s ∪ u : Set X) := Subtype.val ⁻¹' s
  let U : Set (s ∪ u : Set X) := Subtype.val ⁻¹' u
  have hcS : ContinuousOn F S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : S =>
        (⟨e ⟨x.val.val, x.property⟩, Or.inl (e ⟨x.val.val, x.property⟩).property⟩ :
          (t ∪ v : Set Y))) := by fun_prop
    convert hc using 1
    funext x
    exact hFs ⟨x.val.val, x.property⟩
  have hcU : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : U =>
        (⟨f ⟨x.val.val, x.property⟩, Or.inr (f ⟨x.val.val, x.property⟩).property⟩ :
          (t ∪ v : Set Y))) := by fun_prop
    convert hc using 1
    funext x
    exact hFu ⟨x.val.val, x.property⟩
  have hcover : S ∪ U = univ := eq_univ_of_forall fun x => x.property
  have hc : Continuous F := by
    have h := hcS.union_of_isClosed hcU hs hu
    rw [hcover] at h
    exact continuousOn_univ.mp h
  have hcross (x : s) (y : u) (hxy : (e x : Y) = f y) : (x : X) = y := by
    have hxu : (x : X) ∈ u := (hoverlap x).mpr (hxy.symm ▸ (f y).property)
    have heq : f ⟨x, hxu⟩ = f y := Subtype.ext ((hagree x x.property hxu).symm.trans hxy)
    exact congrArg Subtype.val (f.injective heq)
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    · have heq := congrArg Subtype.val hxy
      rw [hFs ⟨x, hx⟩, hFs ⟨y, hy⟩] at heq
      exact congrArg (fun z : s => (z : X)) (e.injective (Subtype.ext heq))
    · have heq := congrArg Subtype.val hxy
      rw [hFs ⟨x, hx⟩, hFu ⟨y, hy⟩] at heq
      exact hcross ⟨x, hx⟩ ⟨y, hy⟩ heq
    · have heq := congrArg Subtype.val hxy
      rw [hFu ⟨x, hx⟩, hFs ⟨y, hy⟩] at heq
      exact (hcross ⟨y, hy⟩ ⟨x, hx⟩ heq.symm).symm
    · have heq := congrArg Subtype.val hxy
      rw [hFu ⟨x, hx⟩, hFu ⟨y, hy⟩] at heq
      exact congrArg (fun z : u => (z : X)) (f.injective (Subtype.ext heq))
  have hsurj : Function.Surjective F := by
    intro y
    rcases y.property with hy | hy
    · let x := e.symm ⟨y, hy⟩
      refine ⟨⟨x, Or.inl x.property⟩, ?_⟩
      rw [hFs]
      apply Subtype.ext
      exact congrArg (fun z : t => (z : Y)) (e.apply_symm_apply ⟨y, hy⟩)
    · let x := f.symm ⟨y, hy⟩
      refine ⟨⟨x, Or.inr x.property⟩, ?_⟩
      rw [hFu]
      apply Subtype.ext
      exact congrArg (fun z : v => (z : Y)) (f.apply_symm_apply ⟨y, hy⟩)
  let E := Equiv.ofBijective F ⟨hinj, hsurj⟩
  have hEt (y : t) : E.symm ⟨y, Or.inl y.property⟩ =
      ⟨e.symm y, Or.inl (e.symm y).property⟩ := by
    apply E.injective
    rw [E.apply_symm_apply]
    change (⟨y, Or.inl y.property⟩ : (t ∪ v : Set Y)) =
      F ⟨e.symm y, Or.inl (e.symm y).property⟩
    rw [hFs, e.apply_symm_apply]
  have hEv (y : v) : E.symm ⟨y, Or.inr y.property⟩ =
      ⟨f.symm y, Or.inr (f.symm y).property⟩ := by
    apply E.injective
    rw [E.apply_symm_apply]
    change (⟨y, Or.inr y.property⟩ : (t ∪ v : Set Y)) =
      F ⟨f.symm y, Or.inr (f.symm y).property⟩
    rw [hFu, f.apply_symm_apply]
  let T : Set (t ∪ v : Set Y) := Subtype.val ⁻¹' t
  let V : Set (t ∪ v : Set Y) := Subtype.val ⁻¹' v
  have hiT : ContinuousOn E.symm T := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hi : Continuous (fun y : T =>
        (⟨e.symm ⟨y.val.val, y.property⟩,
          Or.inl (e.symm ⟨y.val.val, y.property⟩).property⟩ : (s ∪ u : Set X))) := by
      fun_prop
    convert hi using 1
    funext y
    exact hEt ⟨y.val.val, y.property⟩
  have hiV : ContinuousOn E.symm V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hi : Continuous (fun y : V =>
        (⟨f.symm ⟨y.val.val, y.property⟩,
          Or.inr (f.symm ⟨y.val.val, y.property⟩).property⟩ : (s ∪ u : Set X))) := by
      fun_prop
    convert hi using 1
    funext y
    exact hEv ⟨y.val.val, y.property⟩
  have htarget : T ∪ V = univ := eq_univ_of_forall fun y => y.property
  have hi : Continuous E.symm := by
    have h := hiT.union_of_isClosed hiV ht hv
    rw [htarget] at h
    exact continuousOn_univ.mp h
  let H : (s ∪ u : Set X) ≃ₜ (t ∪ v : Set Y) :=
    { toEquiv := E, continuous_toFun := hc, continuous_invFun := hi }
  exact ⟨H, fun x => congrArg Subtype.val (hFs x),
    fun x => congrArg Subtype.val (hFu x)⟩

theorem exists_open_cap_chart_of_closed_halves
    (hsource : IsOpen (s ∪ u)) (htarget : IsOpen (t ∪ v))
    (hne : (s ∪ u).Nonempty)
    (hs : IsClosed ((Subtype.val : (s ∪ u : Set X) → X) ⁻¹' s))
    (hu : IsClosed ((Subtype.val : (s ∪ u : Set X) → X) ⁻¹' u))
    (ht : IsClosed ((Subtype.val : (t ∪ v : Set Y) → Y) ⁻¹' t))
    (hv : IsClosed ((Subtype.val : (t ∪ v : Set Y) → Y) ⁻¹' v))
    (e : s ≃ₜ t) (f : u ≃ₜ v)
    (hoverlap : ∀ x : s, (x : X) ∈ u ↔ (e x : Y) ∈ v)
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x, hxs⟩ : Y) = (f ⟨x, hxu⟩ : Y)) :
    ∃ H : OpenPartialHomeomorph X Y,
      H.source = s ∪ u ∧ H.target = t ∪ v ∧
      (∀ x : s, H x = (e x : Y)) ∧ (∀ x : u, H x = (f x : Y)) := by
  obtain ⟨E, hEs, hEu⟩ := closed_piece_homeomorph hs hu ht hv e f hoverlap hagree
  let : Nonempty (s ∪ u : Set X) := hne.to_subtype
  let : Nonempty (t ∪ v : Set Y) := ⟨E (Classical.choice hne.to_subtype)⟩
  let a := hsource.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : (s ∪ u : Set X) → X)
  let b := htarget.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : (t ∪ v : Set Y) → Y)
  let H := (a.symm.transHomeomorph E).trans b
  have has : a.source = univ := rfl
  have hbs : b.source = univ := rfl
  have hat : a.target = s ∪ u := by
    simp [a]
    rfl
  have hbt : b.target = t ∪ v := by
    simp [b]
    rfl
  have hval (x : (s ∪ u : Set X)) : H x = (E x : Y) := by
    change (E (a.symm (a x)) : Y) = (E x : Y)
    rw [a.left_inv (has.symm ▸ mem_univ x)]
  refine ⟨H, ?_, ?_, fun x => (hval ⟨x, Or.inl x.property⟩).trans (hEs x),
    fun x => (hval ⟨x, Or.inr x.property⟩).trans (hEu x)⟩
  · ext x
    change (x ∈ a.target ∧ E (a.symm x) ∈ b.source) ↔ x ∈ s ∪ u
    simp only [hat, hbs, mem_univ, and_true]
  · ext y
    change (y ∈ b.target ∧ E.symm (b.symm y) ∈ a.source) ↔ y ∈ t ∪ v
    simp only [hbt, has, mem_univ, and_true]

end PoincareConjecture.M76
