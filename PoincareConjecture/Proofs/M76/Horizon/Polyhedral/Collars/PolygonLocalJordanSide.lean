import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalLineModel
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

theorem local_jordan_side_labels {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {q : ℝ × ℝ} (hq : q ∈ P.boundary ℝ)
    {U L R : Set (ℝ × ℝ)} (hU : IsOpen U) (hqU : q ∈ U)
    (hL : IsPreconnected L) (hR : IsPreconnected R)
    (hcover : U \ P.boundary ℝ = L ∪ R) :
    (L ⊆ P.inside ∧ R ⊆ P.outside) ∨
      (R ⊆ P.inside ∧ L ⊆ P.outside) := by
  have hLcomp : L ⊆ (P.boundary ℝ)ᶜ := by
    intro x hx
    have hx' : x ∈ U \ P.boundary ℝ := hcover.symm ▸ Or.inl hx
    exact hx'.2
  have hRcomp : R ⊆ (P.boundary ℝ)ᶜ := by
    intro x hx
    have hx' : x ∈ U \ P.boundary ℝ := hcover.symm ▸ Or.inr hx
    exact hx'.2
  have hinside_open := P.isOpen_inside hP hinj
  have houtside_open := P.isOpen_outside hP hinj
  have hfrontI := P.frontier_inside hP hinj
  have hfrontO := P.frontier_outside hP hinj
  have hqI : q ∈ closure P.inside := frontier_subset_closure (hfrontI.symm ▸ hq)
  have hqO : q ∈ closure P.outside := frontier_subset_closure (hfrontO.symm ▸ hq)
  have hmeetI : ((U ∩ P.inside).Nonempty) := by
    obtain ⟨x, hxU, hxI⟩ := mem_closure_iff.mp hqI U hU hqU
    exact ⟨x, hxU, hxI⟩
  obtain ⟨x, hxU, hxI⟩ := hmeetI
  have hxcomp : x ∈ L ∪ R := hcover ▸ ⟨hxU, hxI.1⟩
  have hmeetO : (U ∩ P.outside).Nonempty := by
    obtain ⟨y, hyU, hyO⟩ := mem_closure_iff.mp hqO U hU hqU
    exact ⟨y, hyU, hyO⟩
  obtain ⟨y, hyU, hyO⟩ := hmeetO
  have hycomp : y ∈ L ∪ R := hcover ▸ ⟨hyU, hyO.1⟩
  have hLs := hL.subset_or_subset hinside_open houtside_open P.disjoint_inside_outside
    (hLcomp.trans P.compl_boundary_eq_inside_union_outside.subset)
  have hRs := hR.subset_or_subset hinside_open houtside_open P.disjoint_inside_outside
    (hRcomp.trans P.compl_boundary_eq_inside_union_outside.subset)
  rcases hLs with hLi | hLo <;> rcases hRs with hRi | hRo
  · exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside
      (hycomp.elim (fun h => hLi h) (fun h => hRi h)) hyO)
  · exact Or.inl ⟨hLi, hRo⟩
  · exact Or.inr ⟨hRi, hLo⟩
  · exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside hxI
      (hxcomp.elim (fun h => hLo h) (fun h => hRo h)))

theorem exists_local_jordan_side_labels {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {q : ℝ × ℝ} (hq : q ∈ P.boundary ℝ) :
    ∃ U L R : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧
      IsPreconnected L ∧ IsPreconnected R ∧
      U \ P.boundary ℝ = L ∪ R ∧
      (L ⊆ P.inside ∧ R ⊆ P.outside ∨
        R ⊆ P.inside ∧ L ⊆ P.outside) := by
  obtain ⟨e, he, hlocal⟩ := P.exists_local_line_model hP hinj hq
  obtain ⟨U, L, R, hU, hqU, hL, hR, hcover, _, _⟩ :=
    e.exists_local_complementary_sides he hlocal
  exact ⟨U, L, R, hU, hqU, hL, hR, hcover,
    P.local_jordan_side_labels hP hinj hq hU hqU hL hR hcover⟩

theorem exists_local_jordan_half_rectangles {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {q : ℝ × ℝ} (hq : q ∈ P.boundary ℝ) :
    ∃ (e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (δ : ℝ), 0 < δ ∧ (e q).2 = 0 ∧
      let J := Ioo ((e q).1 - δ) ((e q).1 + δ)
      let U := e ⁻¹' (J ×ˢ Ioo (-δ) δ)
      let L := e ⁻¹' (J ×ˢ Ioo (-δ) 0)
      let R := e ⁻¹' (J ×ˢ Ioo 0 δ)
      (∀ x ∈ U, x ∈ P.boundary ℝ ↔ (e x).2 = 0) ∧
        ((L ⊆ P.inside ∧ R ⊆ P.outside) ∨
          (R ⊆ P.inside ∧ L ⊆ P.outside)) := by
  obtain ⟨e, he, hlocal⟩ := P.exists_local_line_model hP hinj hq
  have ht : ∀ᶠ y in 𝓝 (e q), e.symm y ∈ P.boundary ℝ ↔ y.2 = 0 := by
    have he' : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
      simpa only [Homeomorph.symm_apply_apply] using e.symm.continuous.tendsto (e q)
    simpa only [Homeomorph.apply_symm_apply] using he'.eventually hlocal
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
  let J := Ioo ((e q).1 - δ) ((e q).1 + δ)
  let U := e ⁻¹' (J ×ˢ Ioo (-δ) δ)
  let L := e ⁻¹' (J ×ˢ Ioo (-δ) 0)
  let R := e ⁻¹' (J ×ˢ Ioo 0 δ)
  have hmodel (x : ℝ × ℝ) (hx : x ∈ U) :
      x ∈ P.boundary ℝ ↔ (e x).2 = 0 := by
    have hmem : e x ∈ Metric.ball (e q) δ := by
      rw [← Prod.eta (e q), ← ball_prod_same, Real.ball_eq_Ioo,
        Real.ball_eq_Ioo, he, zero_sub, zero_add]
      exact hx
    simpa only [mem_ofPred_eq, Homeomorph.symm_apply_apply] using hball hmem
  have hleft : L ⊆ U := fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans hδ⟩
  have hright : R ⊆ U := fun _ hx => ⟨hx.1, (neg_lt_zero.mpr hδ).trans hx.2.1, hx.2.2⟩
  have hqU : q ∈ U := by
    change (e q).1 ∈ J ∧ (e q).2 ∈ Ioo (-δ) δ
    rw [he]
    exact ⟨⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩, neg_lt_zero.mpr hδ, hδ⟩
  have hcover : U \ P.boundary ℝ = L ∪ R := by
    ext x
    constructor
    · rintro ⟨hxU, hxP⟩
      have hne : (e x).2 ≠ 0 := fun h => hxP ((hmodel x hxU).mpr h)
      rcases lt_or_gt_of_ne hne with hl | hr
      · exact Or.inl ⟨hxU.1, hxU.2.1, hl⟩
      · exact Or.inr ⟨hxU.1, hr, hxU.2.2⟩
    · rintro (hl | hr)
      · exact ⟨hleft hl, fun hx => hl.2.2.ne ((hmodel x (hleft hl)).mp hx)⟩
      · exact ⟨hright hr, fun hx => hr.2.1.ne' ((hmodel x (hright hr)).mp hx)⟩
  exact ⟨e, δ, hδ, he, hmodel,
    P.local_jordan_side_labels hP hinj hq
      ((isOpen_Ioo.prod isOpen_Ioo).preimage e.continuous) hqU
      (e.isPreconnected_preimage.mpr (isPreconnected_Ioo.prod isPreconnected_Ioo))
      (e.isPreconnected_preimage.mpr (isPreconnected_Ioo.prod isPreconnected_Ioo)) hcover⟩

end Polygon
