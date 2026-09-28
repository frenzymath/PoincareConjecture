import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedSourceGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OpenSourceCopy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Fibers.RetainedRelation

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Left" => Set.prod Q (Icc (-1 : ℝ) (-1 / 2))
local notation "Middle" => Set.prod Q (Icc (-1 / 2 : ℝ) 0)
local notation "Right" => Set.prod Q (Icc (0 : ℝ) 1)




theorem exists_nested_retained_open_source
    {X : Type*} {f : P2 → X} {g : (V2 × ℝ) → X}
    {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hnested : closure B₁.outer.inside ⊆ B₀.inner.inside)
    (htrace₀ : ∀ p : squareAnnulus l₀ r₀,
      (B₀.chart p : P2) ∈ doubleLocusOn f (squareAnnulus L d) → depth l₀ p = 0)
    (htrace₁ : ∀ p : squareAnnulus l₁ r₁,
      (B₁.chart p : P2) ∈ doubleLocusOn f (squareAnnulus L d) → depth l₁ p = 0)
    (outer : Cyl ≃ₜ (annulusSquare L (-d) \ B₀.outer.inside : Set P2))
    (inner : Cyl ≃ₜ (closure B₁.inner.inside \ interior (annulusSquare L d) : Set P2))
    (copyO : (annulusSquare L (-d) \ B₀.outer.inside : Set P2) ≃ₜ Left)
    (copyI : (closure B₁.inner.inside \ interior (annulusSquare L d) : Set P2) ≃ₜ Right)
    (hcopyO : copyO.IsFinitePL) (hcopyI : copyI.IsFinitePL)
    (hOU : annulusSquare L (-d) \ B₀.outer.inside ⊆ squareAnnulus L d)
    (hIU : closure B₁.inner.inside \ interior (annulusSquare L d) ⊆ squareAnnulus L d)
    (houter : ∀ x : Cyl, (outer x : P2) ∈ A₀ ∪ A₁ ↔ x.val.2 = 1)
    (hinner : ∀ x : Cyl, (inner x : P2) ∈ A₀ ∪ A₁ ↔ x.val.2 = -1)
    (hlevelO : ∀ x, (copyO x).val.2 = ((outer.symm x).val.2 - 3) / 4)
    (hlevelI : ∀ x, (copyI x).val.2 = ((inner.symm x).val.2 + 1) / 2)
    (hkeepO : ∀ x, g (copyO x) = f x) (hkeepI : ∀ x, g (copyI x) = f x)
    (hsingle : ∀ z ∈ Middle, ∀ w ∈ Cyl, g w = g z → w = z) :
    let K := (annulusSquare L (-d) \ B₀.outer.inside) ∪
      (closure B₁.inner.inside \ interior (annulusSquare L d))
    ∃ (j : K → V2 × ℝ) (U : Set P2) (V : Set (V2 × ℝ)) (H : U ≃ₜ V),
      Function.Injective j ∧ Continuous j ∧
      (∃ J : P2 → V2 × ℝ, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x) ∧
      (∀ x, g (j x) = f x) ∧
      (∀ x : (annulusSquare L (-d) \ B₀.outer.inside : Set P2),
        j ⟨x, Or.inl x.property⟩ = (copyO x : V2 × ℝ)) ∧
      (∀ x : (closure B₁.inner.inside \ interior (annulusSquare L d) : Set P2),
        j ⟨x, Or.inr x.property⟩ = (copyI x : V2 × ℝ)) ∧
      range j = Left ∪ Right ∧ (∀ x, j x ∈ Cyl) ∧
      {v : (V2 × ℝ) × (V2 × ℝ) |
        v.1 ∈ Cyl ∧ v.2 ∈ Cyl ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (j v.1, j v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn g Cyl =
        j '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      U ⊆ K ∧ V ⊆ Cyl ∧
      IsOpen ((Subtype.val : squareAnnulus L d → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : Cyl → V2 × ℝ) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ K, (H x : V2 × ℝ) = j ⟨x, hx⟩) ∧
      (∀ x : U, g (H x) = f x) ∧
      (∀ x : K, (x : P2) ∈ doubleLocusOn f (squareAnnulus L d) → (x : P2) ∈ U) ∧
      doubleLocusOn g Cyl ⊆ V := by
  dsimp only
  let O := annulusSquare L (-d) \ B₀.outer.inside
  let I := closure B₁.inner.inside \ interior (annulusSquare L d)
  let K := O ∪ I
  let B := closure B₀.outer.inside \ B₁.inner.inside
  have hdis : Disjoint O I := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hx.2 (B₀.nested (subset_closure (hnested (subset_closure (B₁.nested hy.1)))))
  obtain ⟨j, hji, hjc, hjPL, hjO, hjI, hjrange, hjmaps, hjkeep, hjrel, hjdouble⟩ :=
    exists_resolving_retained_copy_relation hdis copyO copyI hcopyO hcopyI
      hkeepO hkeepI hsingle
  have hcompact : IsCompact K := hcopyO.choose_spec.1.isCompact.union
    hcopyI.choose_spec.1.isCompact
  obtain ⟨hB, hcover, havoid⟩ := nested_retained_closed_band B₀ B₁ hr₀ hr₁ htrace₀ htrace₁
  have hAB : A₀ ∪ A₁ ⊆ B := by
    intro x hx
    rcases hx with hx | hx
    · refine ⟨(B₀.carrier.subset hx).1, ?_⟩
      intro hh
      exact (B₀.carrier.subset hx).2
        (hnested (subset_closure (B₁.nested (subset_closure hh))))
    · exact ⟨subset_closure (B₀.nested (subset_closure (hnested (B₁.carrier.subset hx).1))),
        (B₁.carrier.subset hx).2⟩
  have hcontact : ∀ x : K, j x ∈ Middle → (x : P2) ∈ B := by
    intro x hx
    rcases x.property with ho | hi
    · have hcopy : j x = (copyO ⟨x, ho⟩ : V2 × ℝ) := hjO ⟨x, ho⟩
      rw [hcopy] at hx
      have hheight := hlevelO ⟨x, ho⟩
      have hbound := (copyO ⟨x, ho⟩).property.2.2
      have heq : (outer.symm ⟨x, ho⟩).val.2 = 1 := by linarith [hx.2.1]
      have hh := (houter (outer.symm ⟨x, ho⟩)).mpr heq
      apply hAB
      simpa only [Homeomorph.apply_symm_apply] using hh
    · have hcopy : j x = (copyI ⟨x, hi⟩ : V2 × ℝ) := hjI ⟨x, hi⟩
      rw [hcopy] at hx
      have hheight := hlevelI ⟨x, hi⟩
      have hbound := (copyI ⟨x, hi⟩).property.2.1
      have heq : (inner.symm ⟨x, hi⟩).val.2 = -1 := by linarith [hx.2.2]
      have hh := (hinner (inner.symm ⟨x, hi⟩)).mpr heq
      apply hAB
      simpa only [Homeomorph.apply_symm_apply] using hh
  have hnewcover : Cyl ⊆ range j ∪ Middle := by
    rw [hjrange]
    intro z hz
    by_cases hlo : z.2 ≤ -1 / 2
    · exact Or.inl (Or.inl ⟨hz.1, hz.2.1, hlo⟩)
    · by_cases hhi : 0 ≤ z.2
      · exact Or.inl (Or.inr ⟨hz.1, hhi, hz.2.2⟩)
      · exact Or.inr ⟨hz.1, (lt_of_not_ge hlo).le, (lt_of_not_ge hhi).le⟩
  obtain ⟨U, V, H, hUK, hVT, hU, hV, hHj, hHkeep, hcontains, hnew⟩ :=
    exists_retained_open_source_copy (union_subset hOU hIU) hcompact hB
      (isClosed_sphere.prod isClosed_Icc) j hji hjc hjmaps hjkeep hcover hnewcover
      hcontact (fun x hx hb ↦ disjoint_left.mp havoid ⟨x.property, hx⟩ hb) hjdouble
  exact ⟨j, U, V, H, hji, hjc, hjPL, hjkeep, hjO, hjI, hjrange, hjmaps, hjrel, hjdouble,
    hUK, hVT, hU, hV, hHj, hHkeep, hcontains, hnew⟩

end PoincareConjecture.M76.Dehn.Annuli
