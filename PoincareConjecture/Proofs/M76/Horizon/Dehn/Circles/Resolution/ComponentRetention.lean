import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.WholeComponents

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem connected_sides_of_disjoint_closed_collar
    {E : Type*} [TopologicalSpace E] {U A B : Set E}
    (hU : IsPreconnected U) (hA : IsClosed A) (hAB : A ⊆ B)
    (havoid : Disjoint U (B \ interior A)) :
    U ⊆ interior A ∨ U ⊆ Bᶜ := by
  have hfront : frontier A ⊆ B \ interior A := by
    intro x hx
    exact ⟨hAB (hA.closure_eq ▸ hx.1), hx.2⟩
  rcases component_sides_of_disjoint_frontier hU hA (havoid.mono_right hfront)
      with hi | ho
  · exact Or.inl hi
  · exact Or.inr (fun x hx hxB ↦ disjoint_left.mp havoid hx
      ⟨hxB, fun hxint ↦ ho hx (interior_subset hxint)⟩)

private theorem polygon_region_facts {n : ℕ} (P : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P) :
    interior (closure P.inside) = P.inside ∧
      frontier (closure P.inside) = P.boundary ℝ := by
  obtain ⟨_, hi, hf, _⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hPi (convex_univ : Convex ℝ (univ : Set V2))
      (subset_univ _)
  exact ⟨hi, hf⟩

theorem polygon_collar_boundary_subsets {m n : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hIi : Function.Injective I)
    (hnest : closure I.inside ⊆ P.inside) :
    P.boundary ℝ ⊆ closure P.inside \ I.inside ∧
      I.boundary ℝ ⊆ closure P.inside \ I.inside := by
  obtain ⟨hiP, hfP⟩ := polygon_region_facts P hP hPi
  obtain ⟨hiI, hfI⟩ := polygon_region_facts I hI hIi
  constructor
  · intro x hx
    have hxf : x ∈ frontier (closure P.inside) := hfP.symm ▸ hx
    refine ⟨by simpa using hxf.1, ?_⟩
    intro hxI
    exact hxf.2 (hiP.symm ▸ hnest (subset_closure hxI))
  · intro x hx
    have hxf : x ∈ frontier (closure I.inside) := hfI.symm ▸ hx
    have hxI : x ∈ closure I.inside := by simpa using hxf.1
    exact ⟨subset_closure (hnest hxI), fun hxi ↦ hxf.2 (hiI.symm ▸ hxi)⟩

theorem polygon_collar_component_sides {m n : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3))
    (hI : I.HasSimplicialEdges) (hIi : Function.Injective I)
    (hnest : closure I.inside ⊆ P.inside)
    {U : Set V2} (hU : IsPreconnected U)
    (havoid : Disjoint U (closure P.inside \ I.inside)) :
    U ⊆ I.inside ∨ U ⊆ (closure P.inside)ᶜ := by
  have hi := (polygon_region_facts I hI hIi).1
  have h := connected_sides_of_disjoint_closed_collar hU isClosed_closure
    (hnest.trans subset_closure) (by simpa only [hi] using havoid)
  simpa only [hi] using h

theorem polygon_closed_inside_subset_of_boundary_inside {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hboundary : Q.boundary ℝ ⊆ P.inside) : closure Q.inside ⊆ P.inside := by
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let P' := P.affineImage a.toLinearEquiv.toAffineEquiv.toAffineMap
  let Q' := Q.affineImage a.toLinearEquiv.toAffineEquiv.toAffineMap
  have hp := P.affineImage_of_leftInvOn hP hPi
    a.toLinearEquiv.toAffineEquiv.toAffineMap a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ ↦ a.symm_apply_apply _)
  have hq := Q.affineImage_of_leftInvOn hQ hQi
    a.toLinearEquiv.toAffineEquiv.toAffineMap a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ ↦ a.symm_apply_apply _)
  have hb : Q'.boundary ℝ ⊆ P'.inside := by
    rw [Polygon.affineImage_boundary, Polygon.inside_linearImage]
    exact image_mono hboundary
  have h := P'.closure_inside_subset_inside_of_boundary_subset_inside Q'
    hp.2.1 hp.1 hq.2.1 hq.1 hb
  change closure (Q.affineImage _).inside ⊆ (P.affineImage _).inside at h
  rw [Q.closure_inside_linearImage a, P.inside_linearImage a] at h
  intro x hx
  exact a.injective.mem_set_image.mp (h (mem_image_of_mem a hx))

private theorem polygon_closed_regions_cases {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ)) :
    closure Q.inside ⊆ P.inside ∨ closure P.inside ⊆ Q.inside ∨
      Disjoint (closure P.inside) (closure Q.inside) := by
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let P' := P.affineImage a.toLinearEquiv.toAffineEquiv.toAffineMap
  let Q' := Q.affineImage a.toLinearEquiv.toAffineEquiv.toAffineMap
  have hp := P.affineImage_of_leftInvOn hP hPi
    a.toLinearEquiv.toAffineEquiv.toAffineMap a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ ↦ a.symm_apply_apply _)
  have hq := Q.affineImage_of_leftInvOn hQ hQi
    a.toLinearEquiv.toAffineEquiv.toAffineMap a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ ↦ a.symm_apply_apply _)
  have hd : Disjoint (P'.boundary ℝ) (Q'.boundary ℝ) := by
    rw [Polygon.affineImage_boundary, Polygon.affineImage_boundary]
    exact hdis.image a.injective.injOn (subset_univ _) (subset_univ _)
  have h := P'.closed_inside_nested_or_disjoint Q' hp.2.1 hp.1 hq.2.1 hq.1 hd
  change closure (P.affineImage _).inside ⊆ (Q.affineImage _).inside ∨
    closure (Q.affineImage _).inside ⊆ (P.affineImage _).inside ∨ _ at h
  rw [P.closure_inside_linearImage a, Q.closure_inside_linearImage a,
    P.inside_linearImage a, Q.inside_linearImage a] at h
  rcases h with h | h | h
  · exact Or.inr (Or.inl (fun x hx ↦ a.injective.mem_set_image.mp (h (mem_image_of_mem a hx))))
  · exact Or.inl (fun x hx ↦ a.injective.mem_set_image.mp (h (mem_image_of_mem a hx)))
  · exact Or.inr (Or.inr (disjoint_left.mpr (fun x hx hy ↦
      disjoint_left.mp h (mem_image_of_mem a hx) (mem_image_of_mem a hy))))

private theorem polygon_boundary_connected {m : ℕ} (P : Polygon V2 (m + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P) :
    IsConnected (P.boundary ℝ) := by
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let P' := P.affineImage a.toLinearEquiv.toAffineEquiv.toAffineMap
  have hp := P.affineImage_of_leftInvOn hP hPi
    a.toLinearEquiv.toAffineEquiv.toAffineMap a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ ↦ a.symm_apply_apply _)
  have h := (P'.isConnected_boundary hp.2.1 hp.1).image a.symm a.symm.continuous.continuousOn
  simpa only [P', Polygon.affineImage_boundary, image_image, ContinuousLinearEquiv.coe_toLinearEquiv,
    AffineEquiv.coe_toAffineMap, LinearEquiv.coe_toAffineEquiv, a.symm_apply_apply,
    image_id'] using h

theorem disjoint_polygon_collars_source_cases {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hP₀ : P₀.HasSimplicialEdges) (hP₀i : Function.Injective P₀)
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hP₁ : P₁.HasSimplicialEdges) (hP₁i : Function.Injective P₁)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    (hdis : Disjoint (closure P₀.inside \ I₀.inside) (closure P₁.inside \ I₁.inside)) :
    closure P₁.inside ⊆ I₀.inside ∨ closure P₀.inside ⊆ I₁.inside ∨
      Disjoint (closure P₀.inside) (closure P₁.inside) := by
  have hb₀ := (polygon_collar_boundary_subsets P₀ I₀ hP₀ hP₀i hI₀ hI₀i hn₀).1
  have hb₁ := (polygon_collar_boundary_subsets P₁ I₁ hP₁ hP₁i hI₁ hI₁i hn₁).1
  have hside₁ := polygon_collar_component_sides P₀ I₀ hI₀ hI₀i hn₀
    (polygon_boundary_connected P₁ hP₁ hP₁i).isPreconnected (hdis.symm.mono_left hb₁)
  have hside₀ := polygon_collar_component_sides P₁ I₁ hI₁ hI₁i hn₁
    (polygon_boundary_connected P₀ hP₀ hP₀i).isPreconnected (hdis.mono_left hb₀)
  rcases polygon_closed_regions_cases P₀ P₁ hP₀ hP₀i hP₁ hP₁i (hdis.mono hb₀ hb₁)
      with hn | hn | hd
  · rcases hside₁ with hi | ho
    · exact Or.inl (polygon_closed_inside_subset_of_boundary_inside I₀ P₁ hI₀ hI₀i hP₁ hP₁i hi)
    · exact False.elim (ho (P₁.vertex_mem_boundary 0)
        (subset_closure (hn (hb₁ (P₁.vertex_mem_boundary 0)).1)))
  · rcases hside₀ with hi | ho
    · exact Or.inr (Or.inl
        (polygon_closed_inside_subset_of_boundary_inside I₁ P₀ hI₁ hI₁i hP₀ hP₀i hi))
    · exact False.elim (ho (P₀.vertex_mem_boundary 0)
        (subset_closure (hn (hb₀ (P₀.vertex_mem_boundary 0)).1)))
  · exact Or.inr (Or.inr hd)

theorem square_annulus_middle_between_polygons {m n : ℕ} {L d : ℝ}
    (hd : 0 < d) {A : Set V2} (c : squareAnnulus L d ≃ₜ A)
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hIi : Function.Injective I)
    (hcarrier : A = closure P.inside \ I.inside) (reverse : Bool)
    (hout : ∀ p, (c p : V2) ∈ P.boundary ℝ ↔ depth L p = if reverse then d else -d)
    (hin : ∀ p, (c p : V2) ∈ I.boundary ℝ ↔ depth L p = if reverse then -d else d)
    (p : squareAnnulus L d) (hp : depth L p = 0) :
    (c p : V2) ∈ P.inside \ closure I.inside := by
  obtain ⟨hiP, hfP⟩ := polygon_region_facts P hP hPi
  obtain ⟨hiI, hfI⟩ := polygon_region_facts I hI hIi
  have hc := hcarrier.subset (c p).property
  have hnotP : (c p : V2) ∉ P.boundary ℝ := by
    intro h
    have h' := (hout p).mp h
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at h' <;> linarith
  have hnotI : (c p : V2) ∉ I.boundary ℝ := by
    intro h
    have h' := (hin p).mp h
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at h' <;> linarith
  constructor
  · by_contra h
    exact hnotP (hfP ▸ ⟨subset_closure hc.1, fun hx ↦ h (hiP ▸ hx)⟩)
  · intro hx
    exact hnotI (hfI ▸ ⟨subset_closure hx, fun hx ↦ hc.2 (hiI ▸ hx)⟩)

theorem nested_collar_component_location {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    {U : Set V2} (hU : IsPreconnected U) (hUD : U ⊆ D2)
    (havoid₀ : Disjoint U (closure P₀.inside \ I₀.inside))
    (havoid₁ : Disjoint U (closure P₁.inside \ I₁.inside)) :
    U ⊆ I₁.inside ∨ U ⊆ D2 \ closure P₀.inside ∨
      U ⊆ I₀.inside \ closure P₁.inside := by
  rcases polygon_collar_component_sides P₁ I₁ hI₁ hI₁i hn₁ hU havoid₁ with hi | ho₁
  · exact Or.inl hi
  rcases polygon_collar_component_sides P₀ I₀ hI₀ hI₀i hn₀ hU havoid₀ with hi₀ | ho₀
  · exact Or.inr (Or.inr (fun x hx ↦ ⟨hi₀ hx, ho₁ hx⟩))
  · exact Or.inr (Or.inl (fun x hx ↦ ⟨hUD hx, ho₀ hx⟩))

theorem nested_collar_component_retained_or_disjoint {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    {U : Set V2} (hU : IsPreconnected U) (hUD : U ⊆ D2)
    (havoid₀ : Disjoint U (closure P₀.inside \ I₀.inside))
    (havoid₁ : Disjoint U (closure P₁.inside \ I₁.inside)) :
    U ⊆ closure I₁.inside ∪ (D2 \ P₀.inside) ∨
      Disjoint U (closure I₁.inside ∪ (D2 \ P₀.inside)) := by
  rcases nested_collar_component_location P₀ I₀ P₁ I₁ hI₀ hI₀i hI₁ hI₁i hn₀ hn₁
      hU hUD havoid₀ havoid₁ with hi | ho | hm
  · exact Or.inl (fun x hx ↦ Or.inl (subset_closure (hi hx)))
  · exact Or.inl (fun x hx ↦ Or.inr ⟨(ho hx).1,
      fun hxp ↦ (ho hx).2 (subset_closure hxp)⟩)
  · apply Or.inr
    apply disjoint_left.mpr
    intro x hx hk
    rcases hk with hi | ho
    · exact (hm hx).2 (subset_closure (hn₁ hi))
    · exact ho.2 (hn₀ (subset_closure (hm hx).1))

theorem disjoint_collar_component_retained_piece {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    {U : Set V2} (hU : IsPreconnected U) (hUD : U ⊆ D2)
    (havoid₀ : Disjoint U (closure P₀.inside \ I₀.inside))
    (havoid₁ : Disjoint U (closure P₁.inside \ I₁.inside)) :
    U ⊆ I₀.inside ∨ U ⊆ I₁.inside ∨ U ⊆ D2 \ (closure P₀.inside ∪ closure P₁.inside) := by
  rcases polygon_collar_component_sides P₀ I₀ hI₀ hI₀i hn₀ hU havoid₀ with hi | ho₀
  · exact Or.inl hi
  rcases polygon_collar_component_sides P₁ I₁ hI₁ hI₁i hn₁ hU havoid₁ with hi | ho₁
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (fun x hx ↦ ⟨hUD hx, fun h ↦ h.elim (ho₀ hx) (ho₁ hx)⟩))

theorem nested_retained_avoids_closed_band {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    {G : Set V2} (hseams : Disjoint G (P.boundary ℝ ∪ Q.boundary ℝ)) :
    Disjoint ((closure Q.inside ∪ (D2 \ P.inside)) ∩ G)
      (closure P.inside \ Q.inside) := by
  obtain ⟨hiP, hfP⟩ := polygon_region_facts P hP hPi
  obtain ⟨hiQ, hfQ⟩ := polygon_region_facts Q hQ hQi
  apply disjoint_left.mpr
  rintro x ⟨hk, hg⟩ ⟨hPcl, hQnot⟩
  apply disjoint_left.mp hseams hg
  rcases hk with hQcl | ho
  · exact Or.inr (hfQ ▸ ⟨subset_closure hQcl, fun h ↦ hQnot (hiQ ▸ h)⟩)
  · exact Or.inl (hfP ▸ ⟨subset_closure hPcl, fun h ↦ ho.2 (hiP ▸ h)⟩)

theorem disjoint_retained_avoids_closed_collars {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hP₀ : P₀.HasSimplicialEdges) (hP₀i : Function.Injective P₀)
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hP₁ : P₁.HasSimplicialEdges) (hP₁i : Function.Injective P₁)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    (hdis : Disjoint (closure P₀.inside) (closure P₁.inside))
    {G : Set V2} (hseams₀ : Disjoint G (P₀.boundary ℝ ∪ I₀.boundary ℝ))
    (hseams₁ : Disjoint G (P₁.boundary ℝ ∪ I₁.boundary ℝ)) :
    Disjoint (((closure I₀.inside ∪ closure I₁.inside) ∪
      (D2 \ (P₀.inside ∪ P₁.inside))) ∩ G)
      ((closure P₀.inside \ I₀.inside) ∪ (closure P₁.inside \ I₁.inside)) := by
  have h₀ := nested_retained_avoids_closed_band P₀ I₀ hP₀ hP₀i hI₀ hI₀i hseams₀
  have h₁ := nested_retained_avoids_closed_band P₁ I₁ hP₁ hP₁i hI₁ hI₁i hseams₁
  apply disjoint_left.mpr
  rintro x ⟨hk, hg⟩ (hc₀ | hc₁)
  · rcases hk with (hi₀ | hi₁) | ho
    · exact disjoint_left.mp h₀ ⟨Or.inl hi₀, hg⟩ hc₀
    · exact disjoint_left.mp hdis hc₀.1 (subset_closure (hn₁ hi₁))
    · exact disjoint_left.mp h₀ ⟨Or.inr ⟨ho.1, fun h ↦ ho.2 (Or.inl h)⟩, hg⟩ hc₀
  · rcases hk with (hi₀ | hi₁) | ho
    · exact disjoint_left.mp hdis (subset_closure (hn₀ hi₀)) hc₁.1
    · exact disjoint_left.mp h₁ ⟨Or.inl hi₁, hg⟩ hc₁
    · exact disjoint_left.mp h₁ ⟨Or.inr ⟨ho.1, fun h ↦ ho.2 (Or.inr h)⟩, hg⟩ hc₁

end Dehn

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem OrdinaryIntervalMarkedModel.actual_collar_component_geometry
    (D : OrdinaryIntervalMarkedModel old i) (j : Fin 2)
    {A : Set V2} {L d : ℝ} (hd : 0 < d) (c : squareAnnulus L d ≃ₜ A)
    (hA : A ⊆ (D.clips j.castSucc).space)
    (hmiddle : (fun p : squareAnnulus L d ↦ (c p : V2)) '' {p | depth L p = 0} =
      old.pieces (if j = 0 then i else old.mate i))
    {m n : ℕ} (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hIi : Function.Injective I)
    (hnest : closure I.inside ⊆ P.inside)
    (hcarrier : A = closure P.inside \ I.inside) (reverse : Bool)
    (hout : ∀ p, (c p : V2) ∈ P.boundary ℝ ↔ depth L p = if reverse then d else -d)
    (hin : ∀ p, (c p : V2) ∈ I.boundary ℝ ↔ depth L p = if reverse then -d else d) :
    old.pieces (if j = 0 then i else old.mate i) ⊆ P.inside \ closure I.inside ∧
      Disjoint (doubleLocusOn f D2) (P.boundary ℝ ∪ I.boundary ℝ) ∧
      ∀ k, k ≠ (if j = 0 then i else old.mate i) →
        Disjoint (old.pieces k) (closure P.inside \ I.inside) := by
  have hstrict : old.pieces (if j = 0 then i else old.mate i) ⊆
      P.inside \ closure I.inside := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hmiddle.symm.subset hx
    exact _root_.Dehn.square_annulus_middle_between_polygons hd c P I hP hPi hI hIi
      hcarrier reverse hout hin p hp
  have htrace (x : V2) (hx : x ∈ A) (hd : x ∈ doubleLocusOn f D2) :
      x ∈ old.pieces (if j = 0 then i else old.mate i) :=
    (D.clip_inter_double_locus j).subset ⟨hA hx, hd⟩
  have hb := _root_.Dehn.polygon_collar_boundary_subsets P I hP hPi hI hIi hnest
  refine ⟨hstrict, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hx hxb
    have hxA : x ∈ A := hcarrier.symm.subset (hxb.elim (fun h => hb.1 h) (fun h => hb.2 h))
    obtain ⟨p, hp, hpx⟩ := hmiddle.symm.subset (htrace x hxA hx)
    change (c p : V2) = x at hpx
    change depth L (p : (ℝ × ℝ)) = 0 at hp
    rcases hxb with hxP | hxI
    · have hxp : (c p : V2) ∈ P.boundary ℝ := by rw [hpx]; exact hxP
      have h := (hout p).mp hxp
      cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> linarith [hp]
    · have hxi : (c p : V2) ∈ I.boundary ℝ := by rw [hpx]; exact hxI
      have h := (hin p).mp hxi
      cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> linarith [hp]
  · intro k hk
    apply disjoint_left.mpr
    intro x hx hxC
    exact disjoint_left.mp (old.disjoint hk) hx
      (htrace x (hcarrier.symm.subset hxC) (old.piece_subset_double k hx))

theorem OrdinaryDoubleCurveModel.nested_collar_retention
    (old : OrdinaryDoubleCurveModel e f R) (a b : old.Index)
    {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hP₀ : P₀.HasSimplicialEdges) (hP₀i : Function.Injective P₀)
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    (hnested : closure P₁.inside ⊆ I₀.inside)
    (hselected₀ : old.pieces a ⊆ P₀.inside \ closure I₀.inside)
    (hselected₁ : old.pieces b ⊆ P₁.inside \ closure I₁.inside)
    (havoid₀ : ∀ k, k ≠ a → Disjoint (old.pieces k) (closure P₀.inside \ I₀.inside))
    (havoid₁ : ∀ k, k ≠ b → Disjoint (old.pieces k) (closure P₁.inside \ I₁.inside))
    (hseam₀ : Disjoint (doubleLocusOn f D2) (P₀.boundary ℝ ∪ I₀.boundary ℝ))
    (hseam₁ : Disjoint (doubleLocusOn f D2) (P₁.boundary ℝ ∪ I₁.boundary ℝ)) :
    let K := closure I₁.inside ∪ (D2 \ P₀.inside)
    (∀ k, old.pieces k ⊆ K ∨ Disjoint (old.pieces k) K) ∧
      Disjoint (old.pieces a ∪ old.pieces b) K ∧
      ¬ old.pieces a ⊆ K ∧ ¬ old.pieces b ⊆ K ∧
      Disjoint (K ∩ doubleLocusOn f D2) (closure P₀.inside \ I₁.inside) := by
  let K := closure I₁.inside ∪ (D2 \ P₀.inside)
  have ha : Disjoint (old.pieces a) K := by
    apply disjoint_left.mpr
    intro x hx hk
    rcases hk with hi | ho
    · exact (hselected₀ hx).2 (subset_closure (hnested (subset_closure (hn₁ hi))))
    · exact ho.2 (hselected₀ hx).1
  have hb : Disjoint (old.pieces b) K := by
    apply disjoint_left.mpr
    intro x hx hk
    rcases hk with hi | ho
    · exact (hselected₁ hx).2 hi
    · exact ho.2 (hn₀ (subset_closure (hnested (subset_closure (hselected₁ hx).1))))
  refine ⟨?_, disjoint_union_left.mpr ⟨ha, hb⟩, ?_, ?_, ?_⟩
  · intro k
    by_cases hka : k = a
    · exact Or.inr (hka ▸ ha)
    by_cases hkb : k = b
    · exact Or.inr (hkb ▸ hb)
    exact _root_.Dehn.nested_collar_component_retained_or_disjoint
      P₀ I₀ P₁ I₁ hI₀ hI₀i hI₁ hI₁i hn₀ hn₁ (old.connected k).isPreconnected
      (fun x hx ↦ (old.piece_subset_double k hx).1) (havoid₀ k hka) (havoid₁ k hkb)
  · intro h
    obtain ⟨x, hx⟩ := (old.connected a).nonempty
    exact disjoint_left.mp ha hx (h hx)
  · intro h
    obtain ⟨x, hx⟩ := (old.connected b).nonempty
    exact disjoint_left.mp hb hx (h hx)
  · apply _root_.Dehn.nested_retained_avoids_closed_band P₀ I₁ hP₀ hP₀i hI₁ hI₁i
    exact disjoint_union_right.mpr
      ⟨hseam₀.mono_right subset_union_left, hseam₁.mono_right subset_union_right⟩

theorem OrdinaryDoubleCurveModel.disjoint_collar_retention
    (old : OrdinaryDoubleCurveModel e f R) (a b : old.Index)
    {m₀ n₀ m₁ n₁ : ℕ}
    (P₀ : Polygon V2 (m₀ + 3)) (I₀ : Polygon V2 (n₀ + 3))
    (P₁ : Polygon V2 (m₁ + 3)) (I₁ : Polygon V2 (n₁ + 3))
    (hP₀ : P₀.HasSimplicialEdges) (hP₀i : Function.Injective P₀)
    (hI₀ : I₀.HasSimplicialEdges) (hI₀i : Function.Injective I₀)
    (hP₁ : P₁.HasSimplicialEdges) (hP₁i : Function.Injective P₁)
    (hI₁ : I₁.HasSimplicialEdges) (hI₁i : Function.Injective I₁)
    (hn₀ : closure I₀.inside ⊆ P₀.inside) (hn₁ : closure I₁.inside ⊆ P₁.inside)
    (hdis : Disjoint (closure P₀.inside) (closure P₁.inside))
    (hselected₀ : old.pieces a ⊆ P₀.inside \ closure I₀.inside)
    (hselected₁ : old.pieces b ⊆ P₁.inside \ closure I₁.inside)
    (havoid₀ : ∀ k, k ≠ a → Disjoint (old.pieces k) (closure P₀.inside \ I₀.inside))
    (havoid₁ : ∀ k, k ≠ b → Disjoint (old.pieces k) (closure P₁.inside \ I₁.inside))
    (hseam₀ : Disjoint (doubleLocusOn f D2) (P₀.boundary ℝ ∪ I₀.boundary ℝ))
    (hseam₁ : Disjoint (doubleLocusOn f D2) (P₁.boundary ℝ ∪ I₁.boundary ℝ)) :
    let K := (closure I₀.inside ∪ closure I₁.inside) ∪ (D2 \ (P₀.inside ∪ P₁.inside))
    (∀ k, old.pieces k ⊆ K ∨ Disjoint (old.pieces k) K) ∧
      (∀ k, k ≠ a → k ≠ b → old.pieces k ⊆ K) ∧
      Disjoint (old.pieces a ∪ old.pieces b) K ∧
      ¬ old.pieces a ⊆ K ∧ ¬ old.pieces b ⊆ K ∧
      Disjoint (K ∩ doubleLocusOn f D2)
        ((closure P₀.inside \ I₀.inside) ∪ (closure P₁.inside \ I₁.inside)) := by
  let K := (closure I₀.inside ∪ closure I₁.inside) ∪ (D2 \ (P₀.inside ∪ P₁.inside))
  have ha : Disjoint (old.pieces a) K := by
    apply disjoint_left.mpr
    intro x hx hk
    rcases hk with (hi₀ | hi₁) | ho
    · exact (hselected₀ hx).2 hi₀
    · exact disjoint_left.mp hdis (subset_closure (hselected₀ hx).1)
        (subset_closure (hn₁ hi₁))
    · exact ho.2 (Or.inl (hselected₀ hx).1)
  have hb : Disjoint (old.pieces b) K := by
    apply disjoint_left.mpr
    intro x hx hk
    rcases hk with (hi₀ | hi₁) | ho
    · exact disjoint_left.mp hdis (subset_closure (hn₀ hi₀))
        (subset_closure (hselected₁ hx).1)
    · exact (hselected₁ hx).2 hi₁
    · exact ho.2 (Or.inr (hselected₁ hx).1)
  have hret (k) (hka : k ≠ a) (hkb : k ≠ b) : old.pieces k ⊆ K := by
    rcases _root_.Dehn.disjoint_collar_component_retained_piece
        P₀ I₀ P₁ I₁ hI₀ hI₀i hI₁ hI₁i hn₀ hn₁ (old.connected k).isPreconnected
        (fun x hx ↦ (old.piece_subset_double k hx).1) (havoid₀ k hka) (havoid₁ k hkb)
        with hi₀ | hi₁ | ho
    · exact fun x hx ↦ Or.inl (Or.inl (subset_closure (hi₀ hx)))
    · exact fun x hx ↦ Or.inl (Or.inr (subset_closure (hi₁ hx)))
    · exact fun x hx ↦ Or.inr ⟨(ho hx).1, fun h ↦ (ho hx).2
        (h.elim (fun h ↦ Or.inl (subset_closure h)) (fun h ↦ Or.inr (subset_closure h)))⟩
  refine ⟨?_, hret, disjoint_union_left.mpr ⟨ha, hb⟩, ?_, ?_, ?_⟩
  · intro k
    by_cases hka : k = a
    · exact Or.inr (hka ▸ ha)
    by_cases hkb : k = b
    · exact Or.inr (hkb ▸ hb)
    exact Or.inl (hret k hka hkb)
  · intro h
    obtain ⟨x, hx⟩ := (old.connected a).nonempty
    exact disjoint_left.mp ha hx (h hx)
  · intro h
    obtain ⟨x, hx⟩ := (old.connected b).nonempty
    exact disjoint_left.mp hb hx (h hx)
  · exact _root_.Dehn.disjoint_retained_avoids_closed_collars P₀ I₀ P₁ I₁
      hP₀ hP₀i hI₀ hI₀i hP₁ hP₁i hI₁ hI₁i hn₀ hn₁ hdis hseam₀ hseam₁

end PoincareConjecture.M76.Dehn
