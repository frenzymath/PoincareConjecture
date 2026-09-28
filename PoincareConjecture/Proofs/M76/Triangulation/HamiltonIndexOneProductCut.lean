import PoincareConjecture.Proofs.M76.Mathlib.ProductStripCutTopology
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePL_proper_product_cut (hdim : Module.finrank ℝ E = 3)
    {R : Set E} (hR : IsClosed R) (c : (V2 × ℝ) → E)
    {eps : ℝ} (heps : 0 < eps)
    (hc : FinitePiecewiseAffineOn c (D2 ×ˢ Icc (-eps) eps))
    (hinj : InjOn c (D2 ×ˢ Icc (-eps) eps))
    (hinto : MapsTo c (D2 ×ˢ Icc (-eps) eps) R)
    (hopen : IsOpen ((Subtype.val : R → E) ⁻¹'
      (c '' (D2 ×ˢ Ioo (-eps) eps)))) :
    let C := c '' (D2 ×ˢ Icc (-(eps / 2)) (eps / 2))
    let U := c '' (D2 ×ˢ Ioo (-(eps / 2)) (eps / 2))
    let ends := c '' (D2 ×ˢ ({-(eps / 2), eps / 2} : Set ℝ))
    IsClosed (R \ U) ∧ interior (R \ U) = interior R \ C ∧
      frontier (R \ U) = (frontier R \ U) ∪ ends ∧
      C ∩ (R \ U) = ends ∧ C ∪ (R \ U) = R ∧
      (interior (R \ U)).Nonempty := by
  let P := D2 ×ˢ Icc (-eps) eps
  let small := D2 ×ˢ Icc (-(eps / 2)) (eps / 2)
  let middle := D2 ×ˢ Ioo (-(eps / 2)) (eps / 2)
  let full := D2 ×ˢ Ioo (-eps) eps
  let edge := D2 ×ˢ ({-(eps / 2), eps / 2} : Set ℝ)
  let outer := (D2 ×ˢ Icc (-eps) (-(eps / 2))) ∪
    (D2 ×ˢ Icc (eps / 2) eps)
  have hsmallP : small ⊆ P := by
    intro x hx
    exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have hmiddleSmall : middle ⊆ small :=
    prod_mono subset_rfl Ioo_subset_Icc_self
  have hfullP : full ⊆ P := prod_mono subset_rfl Ioo_subset_Icc_self
  have hmiddleFull : middle ⊆ full := by
    intro x hx
    exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have houterP : outer ⊆ P := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩
    · exact ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
  have hedgeSmall : edge ⊆ small := by
    intro x hx
    have ht : x.2 = -(eps / 2) ∨ x.2 = eps / 2 := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hx.2
    refine ⟨hx.1, ?_⟩
    rcases ht with ht | ht <;> rw [ht] <;> constructor <;> linarith
  have houterCompact : IsCompact outer :=
    ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc).union
      ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
  have houterClosed : IsClosed (c '' outer) :=
    (houterCompact.image_of_continuousOn (hc.continuousOn.mono houterP)).isClosed
  have hmiddleEq : c '' middle = (c '' full) \ (c '' outer) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hmiddleFull hx, rfl⟩, ?_⟩
      rintro ⟨z, hz, heq⟩
      have hzx := hinj (houterP hz) (hsmallP (hmiddleSmall hx)) heq
      subst z
      rcases hz with hz | hz
      · exact (not_lt_of_ge hz.2.2) hx.2.1
      · exact (not_lt_of_ge hz.2.1) hx.2.2
    · rintro ⟨⟨x, hx, rfl⟩, hout⟩
      refine ⟨x, ⟨hx.1, ?_, ?_⟩, rfl⟩
      · by_contra h
        exact hout ⟨x, Or.inl ⟨hx.1, hx.2.1.le, le_of_not_gt h⟩, rfl⟩
      · by_contra h
        exact hout ⟨x, Or.inr ⟨hx.1, le_of_not_gt h, hx.2.2.le⟩, rfl⟩
  have hmiddleOpen : IsOpen ((Subtype.val : R → E) ⁻¹' (c '' middle)) := by
    rw [hmiddleEq, preimage_sdiff]
    exact hopen.sdiff (houterClosed.preimage continuous_subtype_val)
  have hsmallBall := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
    (isFinitePLBallPair_Icc (show -(eps / 2) < eps / 2 by linarith))
  have hCball := hsmallBall.image_of_subset hc hsmallP hinj
  have hdim' : Module.finrank ℝ (V2 × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have hCU : interior (c '' small) ⊆ c '' middle := by
    intro y hy
    have hys := (hCball.interior_eq_sdiff_of_finrank_eq hdim').subset hy
    obtain ⟨x, hx, rfl⟩ := hys.1
    have hnotend : x.2 ∉ ({-(eps / 2), eps / 2} : Set ℝ) := by
      intro he
      exact hys.2 ⟨x, Or.inr ⟨hx.1, he⟩, rfl⟩
    have hne : x.2 ≠ -(eps / 2) ∧ x.2 ≠ eps / 2 := by
      simpa only [mem_insert_iff, mem_singleton_iff, not_or] using hnotend
    exact ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2.1 hne.1.symm,
      lt_of_le_of_ne hx.2.2 hne.2⟩, rfl⟩
  have htrace : (c '' small) \ (c '' middle) = c '' edge := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
      refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
      have ht : x.2 = -(eps / 2) ∨ x.2 = eps / 2 := by
        by_contra hn
        push Not at hn
        exact hnot ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2.1 hn.1.symm,
          lt_of_le_of_ne hx.2.2 hn.2⟩, rfl⟩
      simpa only [mem_insert_iff, mem_singleton_iff] using ht
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hedgeSmall hx, rfl⟩, ?_⟩
      rintro ⟨z, hz, heq⟩
      have hzx := hinj (hsmallP (hmiddleSmall hz)) (hsmallP (hedgeSmall hx)) heq
      subst z
      have ht : x.2 = -(eps / 2) ∨ x.2 = eps / 2 := by
        simpa only [mem_insert_iff, mem_singleton_iff] using hx.2
      rcases ht with ht | ht <;> linarith [hz.2.1, hz.2.2]
  have hCR : c '' small ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hinto (hsmallP hx)
  obtain ⟨hclosed, hint, hfront, hoverlap, hcover⟩ :=
    physical_strip_cut_geometry hR hCball.isCompact.isClosed hCR
      (image_mono hmiddleSmall) hCU
      (hCball.closure_interior_of_finrank_eq hdim') hmiddleOpen htrace
  refine ⟨hclosed, hint, hfront, hoverlap, hcover, ?_⟩
  rw [hint]
  let x : V2 × ℝ := (0, 3 * eps / 4)
  have hxint : x ∈ interior P := by
    rw [interior_prod_eq, interior_closedBall _ one_ne_zero, interior_Icc]
    exact ⟨mem_ball_self zero_lt_one, by constructor <;> dsimp [x] <;> linarith⟩
  have hPR : c '' P ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact hinto hz
  have hxR : c x ∈ interior R :=
    interior_mono hPR (hc.mem_interior_image hdim' hinj hxint)
  refine ⟨c x, hxR, ?_⟩
  rintro ⟨z, hz, heq⟩
  have hzx := hinj (hsmallP hz) (interior_subset hxint) heq
  subst z
  have hbound := hz.2.2
  change 3 * eps / 4 ≤ eps / 2 at hbound
  linarith

end PoincareConjecture.M76.HamiltonIndexOne
