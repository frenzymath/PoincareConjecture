import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAffineSimplexModel
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOpenSimplexCylinder
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAtlasHandleStep

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

theorem exists_simplex_atlas_handle_step
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (c : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (hcover : ∀ x : X, ∃ i, x ∈ (c i).source)
    (d : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hhandle : ∀ J : Finset (Fin 3), HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J)
    (i0 : ι) (s : Finset (Fin 3 → ℝ)) (hs : s.Nonempty)
    (hindep : AffineIndependent ℝ ((↑) : s → (Fin 3 → ℝ)))
    (hschart : convexHull ℝ (s : Set (Fin 3 → ℝ)) ⊆ (c i0).target)
    {U W P : Set X} (hU : IsOpen U) (hW : IsOpen W) (hP : IsClosed P)
    (hPU : P ⊆ U)
    (hsW : (c i0).symm '' convexHull ℝ (s : Set (Fin 3 → ℝ)) ⊆ W ∩ d.source)
    (hfront : (c i0).symm '' intrinsicFrontier ℝ (convexHull ℝ (s : Set (Fin 3 → ℝ))) ⊆ U)
    (hdis : Disjoint ((c i0).symm ''
      intrinsicInterior ℝ (convexHull ℝ (s : Set (Fin 3 → ℝ)))) P)
    (hUpl : ∀ i, LocallyPiecewiseAffineOn (d ∘ (c i).symm)
      ((c i).target ∩ (c i).symm ⁻¹' U)) :
    ∃ (F : X ≃ₜ X) (V S : Set X),
      IsOpen V ∧ IsCompact S ∧ S ⊆ W ∧ Disjoint S P ∧ EqOn F id Sᶜ ∧
      P ∪ ((c i0).symm '' convexHull ℝ (s : Set (Fin 3 → ℝ))) ⊆ V ∧
      ∀ i, LocallyPiecewiseAffineOn ((d ∘ F) ∘ (c i).symm)
        ((c i).target ∩ (c i).symm ⁻¹' V) := by
  classical
  let C := convexHull ℝ (s : Set (Fin 3 → ℝ))
  let U0 := (c i0).target ∩ (c i0).symm ⁻¹' U
  let V0 := (c i0).target ∩ (c i0).symm ⁻¹' (W ∩ d.source)
  let P0 := ((c i0).target ∩ (c i0).symm ⁻¹' Pᶜ)ᶜ
  have hU0 : IsOpen U0 := (c i0).isOpen_inter_preimage_symm hU
  have hV0 : IsOpen V0 := (c i0).isOpen_inter_preimage_symm (hW.inter d.open_source)
  have hP0 : IsClosed P0 :=
    ((c i0).isOpen_inter_preimage_symm hP.isOpen_compl).isClosed_compl
  obtain ⟨J, Phi, D, h, _, _, _, _, hh, hcarrier, hinterior, hboundary⟩ :=
    exists_affine_simplex_cube_model s hs hindep
  have hpoint (x : J → ℝ) (hx : x ∈ D) : Phi (x, 0) ∈ C := by
    apply hcarrier.subset
    exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  have hDV (x : J → ℝ) (hx : x ∈ D) : Phi (x, 0) ∈ V0 :=
    ⟨hschart (hpoint x hx), hsW (mem_image_of_mem _ (hpoint x hx))⟩
  have hDP (x : J → ℝ) (hx : x ∈ interior D) : Phi (x, 0) ∉ P0 := by
    change ¬ Phi (x, 0) ∉ (c i0).target ∩ (c i0).symm ⁻¹' Pᶜ
    apply not_not.mpr
    refine ⟨hschart (hpoint x (interior_subset hx)), ?_⟩
    exact fun hxp => Set.disjoint_left.mp hdis
      (mem_image_of_mem _ ((hinterior x).mpr hx)) hxp
  have hboundaryU (x : closedBall (0 : J → ℝ) 1) (hx : ‖(x : J → ℝ)‖ = 1) :
      Phi ((h x : J → ℝ), 0) ∈ U0 :=
    ⟨hschart (hpoint _ (h x).property),
      hfront (mem_image_of_mem _ ((hboundary x).mpr hx))⟩
  obtain ⟨p0, N0, hp0, hp0PL, hp0iPL, hp0target, hN0, hN0eq, hfront0, hcoverage⟩ :=
    exists_open_simplex_cylinder J h hh Phi hU0 hV0 hP0 hDV hDP hboundaryU
  have hp0c : p0.target ⊆ (c i0).target := fun _ hx => (hp0target hx).1.1
  let p := p0.trans (c i0).symm
  have hpsource : p.source = p0.source := by
    apply inter_eq_left.mpr
    exact fun x hx => hp0c (p0.map_source hx)
  have hpvalue (x : Fin 3 → ℝ) : p x = (c i0).symm (p0 x) := rfl
  have hptarget : p.target ⊆ (W ∩ d.source) \ P := by
    intro x hx
    have hc0 : x ∈ (c i0).source := hx.1
    have hx0 : (c i0) x ∈ p0.target := hx.2
    have hgood := hp0target hx0
    have hWD : x ∈ W ∩ d.source := by
      have h := hgood.1.2
      change (c i0).symm ((c i0) x) ∈ W ∩ d.source at h
      rwa [(c i0).left_inv hc0] at h
    have hPnot : x ∉ P := by
      have h := not_not.mp hgood.2
      have hxP := h.2
      change (c i0).symm ((c i0) x) ∉ P at hxP
      rwa [(c i0).left_inv hc0] at hxP
    exact ⟨hWD, hPnot⟩
  have hp : coordinateCylinder J ⊆ p.source := hpsource.symm ▸ hp0
  have hpd : p.target ⊆ d.source := fun _ hx => (hptarget hx).1.2
  have hp0mem : p0 ∈ piecewiseAffineGroupoid (Fin 3 → ℝ) := ⟨hp0PL, hp0iPL⟩
  have hcharts (i : ι) : p.trans (c i) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ) := by
    change (p0.trans (c i0).symm).trans (c i) ∈ _
    rw [OpenPartialHomeomorph.trans_assoc]
    exact (piecewiseAffineGroupoid (Fin 3 → ℝ)).trans hp0mem (hcompat i0 i)
  have hchartsF (i : ι) : LocallyPiecewiseAffineOn (p.trans (c i)) (p.trans (c i)).source :=
    ((mem_piecewiseAffineGroupoid_iff _ _).mp (hcharts i)).1
  have hchartsI (i : ι) : LocallyPiecewiseAffineOn ((c i).symm.trans p.symm)
      ((c i).symm.trans p.symm).source :=
    ((mem_piecewiseAffineGroupoid_iff _ _).mp (hcharts i)).2
  let N := p.source ∩ p ⁻¹' U
  have hN : IsOpen N := p.isOpen_inter_preimage hU
  have hNsame : N0 = N := by
    rw [hN0eq]
    ext x
    constructor
    · rintro ⟨hx, hxc, hxU⟩
      exact ⟨hpsource.symm ▸ hx, hxU⟩
    · rintro ⟨hx, hxU⟩
      have hx0 : x ∈ p0.source := hpsource ▸ hx
      exact ⟨hx0, hp0c (p0.map_source hx0), hxU⟩
  have hfrontN : frontier (coordinateCylinder J) ⊆ N := hNsame ▸ hfront0
  have hNpl := locallyPiecewiseAffineOn_incoming_handle_chart c hcover p d hchartsF hU hUpl
  have heSource : (p.trans d).source = p.source := by
    apply inter_eq_left.mpr
    exact fun x hx => hpd (p.map_source hx)
  have hNN : (p.trans d).source ∩ N = N := by
    rw [heSource]
    exact inter_eq_right.mpr inter_subset_left
  obtain ⟨F, V, S, hV, hS, hSp, hFfix, hSformula, hVformula, hVpl⟩ :=
    exists_atlas_supported_handle_step c J (hhandle J) p d hp hpd hchartsI hU hUpl
      hN hfrontN (hNN.symm ▸ hNpl)
  have hSgood : S ⊆ (W ∩ d.source) \ P := hSp.trans hptarget
  have hSP : Disjoint S P := Set.disjoint_left.mpr fun _ hx => (hSgood hx).2
  have hPV : P ⊆ V := by
    intro x hx
    rw [hVformula]
    exact Or.inl ⟨hPU hx, fun hxS => Set.disjoint_left.mp hSP hxS hx⟩
  have hCV : (c i0).symm '' C ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    have hyc : y ∈ (c i0).target := hschart hy
    have hylevel := hcoverage (hcarrier.symm.subset hy)
    rw [hVformula, hNN]
    rcases hylevel with hold | hnew
    · apply Or.inl
      refine ⟨hold.1.2, ?_⟩
      rw [hSformula]
      rintro ⟨x, hx, hxy⟩
      have hx0 : x ∈ p0.source := hp0 hx.1
      have hpxc : p0 x ∈ (c i0).target := hp0c (p0.map_source hx0)
      have heq : p0 x = y := by
        have he := congrArg (c i0) hxy
        change (c i0) ((c i0).symm (p0 x)) = (c i0) ((c i0).symm y) at he
        rwa [(c i0).right_inv hpxc, (c i0).right_inv hyc] at he
      exact hold.2 ⟨x, hx, heq⟩
    · obtain ⟨x, hx, hxy⟩ := hnew
      refine Or.inr ⟨x, ?_, ?_⟩
      · rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr ⟨hNsame ▸ hx.1, hx.2⟩
      · change (c i0).symm (p0 x) = (c i0).symm y
        exact congrArg (c i0).symm hxy
  exact ⟨F, V, S, hV, hS, fun _ hx => (hSgood hx).1.1,
    hSP, hFfix, union_subset hPV hCV, hVpl⟩

end PoincareConjecture.M76
