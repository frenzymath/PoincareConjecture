import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.FixedCoreFilling










set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [RegularSpace Y]




theorem exists_lift_into_regular_image {q : X → Y} (hq : Continuous q) (c : Y)
    {W : Set Y} (R : OpenPartialHomeomorph X Y)
    (hRs : R.source = (q ⁻¹' {c})ᶜ) (hRt : R.target = W \ {c})
    (hRq : EqOn R q R.source) (k : OpenPartialHomeomorph Y Y)
    (hks : k.source = univ) (hkW : k.target ⊆ W)
    {V : Set Y} (hV : IsOpen V) (hc : c ∈ V) (hkfix : EqOn k id V) :
    ∃ H : OpenPartialHomeomorph X X, H.source = univ ∧
      EqOn H id (q ⁻¹' V) ∧ ∀ x, q (H x) = k (q x) := by
  have hkc : k c = c := hkfix hc
  have hksmem (y : Y) : y ∈ k.source := hks.symm ▸ mem_univ y
  have hkne {y : Y} (hy : y ≠ c) : k y ≠ c := by
    intro he
    exact hy (k.injOn (hksmem y) (hksmem c) (he.trans hkc.symm))
  have hRne {x : X} (hx : x ∈ R.source) : R x ≠ c :=
    (hRt ▸ R.map_source hx).2
  have hRqinv {y : Y} (hy : y ∈ R.target) : q (R.symm y) = y :=
    (hRq (R.map_target hy)).symm.trans (R.right_inv hy)
  let e := R.trans (k.trans R.symm)
  have hes : e.source = (q ⁻¹' {c})ᶜ := by
    rw [← hRs]
    ext x
    change (x ∈ R.source ∧ R x ∈ k.source ∧ k (R x) ∈ R.target) ↔ x ∈ R.source
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, hksmem _, hRt.symm ▸
        ⟨hkW (k.map_source (hksmem _)), hkne (hRne hx)⟩⟩
  have hetA : e.target ⊆ (q ⁻¹' {c})ᶜ := by
    intro x hx
    have hxs : x ∈ R.source := hx.1.1
    simpa only [hRs] using hxs
  have hefix : EqOn e id ((q ⁻¹' V) \ (q ⁻¹' {c})) := by
    intro x hx
    have hxs : x ∈ R.source := hRs.symm ▸ hx.2
    have hxV : R x ∈ V := (hRq hxs).symm ▸ hx.1
    change R.symm (k (R x)) = x
    calc
      R.symm (k (R x)) = R.symm (R x) := congrArg R.symm (hkfix hxV)
      _ = x := R.left_inv hxs
  have heq (x : X) (hx : x ∈ e.source) : q (e x) = k (q x) := by
    have hxs : x ∈ R.source := hx.1
    have hxt : k (R x) ∈ R.target := hx.2.2
    change q (R.symm (k (R x))) = k (q x)
    rw [hRqinv hxt, hRq hxs]
  obtain ⟨C, hC, hAC, hCV⟩ := exists_closed_fiber_core hq c hV hc
  have hfixC : EqOn e id (C \ (q ⁻¹' {c})) := by
    intro x hx
    exact hefix ⟨hCV hx.1, hx.2⟩
  have het : e.target = (e.target ∪ C) \ (q ⁻¹' {c}) := by
    ext x
    constructor
    · intro hx
      exact ⟨Or.inl hx, hetA hx⟩
    · rintro ⟨hx | hx, hxc⟩
      · exact hx
      · have hxs : x ∈ e.source := hes.symm ▸ hxc
        have hm := e.map_source hxs
        have he : e x = x := hfixC ⟨hx, hxc⟩
        rwa [he] at hm
  obtain ⟨H, hHs, _, hHC, hHe⟩ := exists_fill_fixed_core e hes het
    hC hAC subset_union_right hfixC
  have hregular {x : X} (hx : x ∉ C) : x ∈ e.source := by
    rw [hes]
    exact fun h => hx (interior_subset (hAC h))
  refine ⟨H, hHs, ?_, ?_⟩
  · intro x hx
    by_cases hxC : x ∈ C
    · exact hHC hxC
    · have hxA : x ∈ (q ⁻¹' {c})ᶜ := by simpa only [hes] using hregular hxC
      exact (hHe hxC).trans (hefix ⟨hx, hxA⟩)
  · intro x
    by_cases hxC : x ∈ C
    · exact (congrArg q (hHC hxC)).trans (hkfix (hCV hxC)).symm
    · exact (congrArg q (hHe hxC)).trans (heq x (hregular hxC))

end OpenPartialHomeomorph
