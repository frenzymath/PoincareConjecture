import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorFace
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryFace

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_surface_face_motion_data
    {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K₁) (hK₁ : K₁ ≤ K)
    {face : Finset V} (hfaceK : face ∈ K.faces)
    (hsource : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    (boundary : Bool) (rimSet : Set V)
    (hphase : (boundary = true → K₁.space ⊆ rimSet) ∧
      (boundary = false → rimSet ⊆ K₀.space))
    {R Fmark W : Set M} (hF : Fmark = frontier R ∩ W)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hjR : MapsTo j K.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ rimSet)
    (Q : OpenPartialHomeomorph t.Carrier E)
    (B : OpenPartialHomeomorph s.Carrier E)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E)
    (htarget : Q.target = B.target)
    (hval : ∀ y, Q y = B (step.projection (step.inclusion y)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    (hmark : boundary = true → Q.source ⊆ t.projection ⁻¹' W)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space)
    (hJQ : J.space ⊆ Q.target)
    (hface : ∀ x ∈ convexHull ℝ (face : Set V),
      j x ∈ Q.source ∧ Q (j x) ∈ interior J.space)
    (hmodel : B.source ⊆ interior (s.projection ⁻¹' R) ∨
      ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
        (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
        ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0)
    (U : K.faces → Set t.Carrier) (hU : ∀ a, IsOpen (U a))
    (hretain : ∀ a : K.faces, MapsTo j (convexHull ℝ (a.val : Set V)) (U a)) :
    Nonempty (MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary) := by
  cases boundary with
  | false =>
    obtain ⟨Jrel, P, P₀, L, ε, hJrel, hrelcv, hrelJ, hactive, hε,
      hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hfront, hL,
      R₀, T, T₀, hR₀, hR₀J, hT, hTs, hT₀, hT₀s, hfull,
      H, hHaff, hHimage, hHfaces,
      G, hG, hGinv, hzero, hformula, hout, hprefix, hGfront, hregion,
      hGPL, hGinvPL, hkeep⟩ :=
      step.exists_interior_surface_face_motion K K₀ K₁ hK hK₀ hK₁ hfaceK hsource
        (hphase.2 rfl) (hF.subset.trans inter_subset_left) hj hjR hproper Q B hQ hB
        htarget hval hmaps J hJ hcv hJQ hface hmodel U hU hretain
    obtain ⟨V, hV, hVs⟩ := hHimage
    exact ⟨{
      support := Jrel
      source := P
      fixedSource := P₀
      targets := L
      plane := ⊤
      support_finite := hJrel
      support_convex := hrelcv
      support_subset := hrelJ
      support_upper := hrelJ.trans hJQ
      support_lower := (hrelJ.trans hJQ).trans htarget.subset
      source_finite := hP
      protected_finite := hP₀
      source_space := hPs
      protected_space := hP₀s
      protected_subset := hP₀P
      source_subset := hPJ
      active_supported := by
        intro x hx hxold
        rcases hsource.subset hx with hxprefix | hxface
        · exact False.elim (hxold hxprefix)
        · exact hactive x hxface hxold
      frontier_protected := hfront
      targets_finite := fun a => (hL a).1
      targets_space := fun a => (hL a).2.1
      targets_card := fun a => (hL a).2.2
      subdivision := R₀
      freeComplex := T
      fixedComplex := T₀
      subdivision_finite := hR₀
      subdivides := hR₀J
      free_le := hT
      free_space := hTs
      fixed_le := hT₀
      fixed_space := hT₀s
      fixed_full := hfull
      epsilon := ε
      epsilon_pos := hε
      coordinates := H
      endpoint_affine := hHaff
      endpointImage := V
      endpointImage_finite := hV
      endpointImage_space := hVs
      position := hHfaces
      boundary_support := fun h => Bool.noConfusion h
      boundary_plane := fun h => Bool.noConfusion h
      interior_plane := fun _ => rfl
      ambient := G
      continuous_ambient := hG
      continuous_inverse := hGinv
      zero := hzero
      chart_formula := hformula
      exterior := hout
      prefix_fixed := hprefix
      region := fun a => (hregion a).1
      mark := fun a => (hregion a).2
      frontier_fixed := fun _ => hGfront
      original_PL := hGPL
      original_inverse_PL := hGinvPL
      retained := hkeep }⟩
  | true =>
    obtain ⟨ell, A, P, P₀, L, ε, hell, hAs, hAdir, hε,
      hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hfront, hPA, hL,
      R₀, T, T₀, hR₀, hR₀J, hT, hTs, hT₀, hT₀s, hfull,
      H, hHaff, hheight, hHimage, hHfaces,
      G, hG, hGinv, hzero, hformula, hout, hprefix, hregion,
      hGPL, hGinvPL, hkeep⟩ :=
      step.exists_boundary_surface_face_motion K K₀ K₁ hK hK₀ hK₁ hfaceK hsource
        hF hj (fun x hx ↦ (hproper x (SimplicialComplex.space_subset_of_le hK₁ hx)).mpr
          (hphase.1 rfl hx)) Q B hQ hB htarget hval hmaps (hmark rfl)
        J hJ hcv hJQ hface hmodel U hU hretain
    obtain ⟨V, hV, hVs⟩ := hHimage
    exact ⟨{
      support := J
      source := P
      fixedSource := P₀
      targets := L
      plane := A
      support_finite := hJ
      support_convex := hcv
      support_subset := Subset.rfl
      support_upper := hJQ
      support_lower := hJQ.trans htarget.subset
      source_finite := hP
      protected_finite := hP₀
      source_space := hPs
      protected_space := hP₀s
      protected_subset := hP₀P
      source_subset := hPJ
      active_supported := by
        intro x hx hxold
        rcases hsource.subset hx with hxprefix | hxface
        · exact False.elim (hxold hxprefix)
        · exact (hface x hxface).2
      frontier_protected := hfront
      targets_finite := fun a => (hL a).1
      targets_space := fun a => (hL a).2.1
      targets_card := fun a => (hL a).2.2.1
      subdivision := R₀
      freeComplex := T
      fixedComplex := T₀
      subdivision_finite := hR₀
      subdivides := hR₀J
      free_le := hT
      free_space := hTs
      fixed_le := hT₀
      fixed_space := hT₀s
      fixed_full := hfull
      epsilon := ε
      epsilon_pos := hε
      coordinates := H
      endpoint_affine := hHaff
      endpointImage := V
      endpointImage_finite := hV
      endpointImage_space := hVs
      position := hHfaces
      boundary_support := fun _ => rfl
      boundary_plane := fun _ =>
        ⟨ell, hell, hAs, hAdir, hPA, fun a => (hL a).2.2.2, hheight⟩
      interior_plane := fun h => Bool.noConfusion h
      ambient := G
      continuous_ambient := hG
      continuous_inverse := hGinv
      zero := hzero
      chart_formula := hformula
      exterior := hout
      prefix_fixed := hprefix
      region := fun a => (hregion a).1
      mark := fun a => (hregion a).2.2
      frontier_fixed := fun h => Bool.noConfusion h
      original_PL := hGPL
      original_inverse_PL := hGinvPL
      retained := hkeep }⟩

end Geometry.OriginalPLTower
