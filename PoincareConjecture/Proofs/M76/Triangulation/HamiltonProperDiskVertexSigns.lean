import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskIncidentFormulas

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

private theorem open_meets_simplex_interior {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {S U : Set X} (hspan : affineSpan ℝ S = ⊤) (hU : IsOpen U)
    {x : X} (hxS : x ∈ convexHull ℝ S) (hxU : x ∈ U) :
    (interior (convexHull ℝ S) ∩ U).Nonempty := by
  have hne : (interior (convexHull ℝ S)).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hxcl : x ∈ closure (interior (convexHull ℝ S)) := by
    rw [(convex_convexHull ℝ S).closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure hxS
  obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.mp hxcl U hU hxU
  exact ⟨y, hyS, hyU⟩

omit [FiniteDimensional ℝ E] in
private theorem original_triangle_span
    (T : HamiltonProperDiskTriangulation R D b)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 3)
    (P : V2 →ᴬ[ℝ] E)
    (hP : ∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x) :
    affineSpan ℝ (T.inverse '' (s : Set E)) = ⊤ := by
  have hcomp : P.toAffineMap ∘ (T.inverse ∘ ((↑) : s → E)) = ((↑) : s → E) := by
    funext x
    exact hP x (subset_convexHull ℝ _ x.property)
  have hind : AffineIndependent ℝ (T.inverse ∘ ((↑) : s → E)) :=
    AffineIndependent.of_comp P.toAffineMap (by rw [hcomp]; exact T.disk.indep hs)
  have hrange : range (T.inverse ∘ ((↑) : s → E)) = T.inverse '' (s : Set E) := by
    ext x
    simp only [mem_range, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← hrange]
  exact hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hcard])

omit [FiniteDimensional ℝ E] in
private theorem original_triangle_values
    (T : HamiltonProperDiskTriangulation R D b)
    {s : Finset E} (hs : s ∈ T.disk.faces)
    (P : V2 →ᴬ[ℝ] E)
    (hP : ∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x)
    (F : V2 → E) (hF : ∀ x : Cube, F x = (b x : E)) :
    convexHull ℝ (T.inverse '' (s : Set E)) ⊆ Cube ∧
      ∀ x ∈ convexHull ℝ (T.inverse '' (s : Set E)),
        P x = F x ∧ P x ∈ convexHull ℝ (s : Set E) := by
  have hvalue (y : E) (hy : y ∈ convexHull ℝ (s : Set E)) :
      T.inverse y ∈ Cube ∧ F (T.inverse y) = y := by
    have hyD : y ∈ D := T.disk_space.subset (T.disk.convexHull_subset_space hs hy)
    have hinv := T.inverse_eq ⟨y, hyD⟩
    constructor
    · rw [hinv]
      exact (b.symm ⟨y, hyD⟩).property
    · rw [hinv, hF (b.symm ⟨y, hyD⟩)]
      exact congrArg Subtype.val (b.apply_symm_apply ⟨y, hyD⟩)
  constructor
  · intro x hx
    rw [← T.inverse_affine.image_convexHull hs] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hvalue y hy).1
  · intro x hx
    rw [← T.inverse_affine.image_convexHull hs] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(hP y hy).trans (hvalue y hy).2.symm, by rwa [hP y hy]⟩

theorem HamiltonProperDiskTriangulation.normal_product_equation_at_vertex
    (T : HamiltonProperDiskTriangulation R D b) (hb : b.IsFinitePL)
    (p : T.disk.vertices) (c : E ≃ᴬ[ℝ] V)
    {s t u v : Finset E} (hs : s ∈ T.disk.faces) (ht : t ∈ T.disk.faces)
    (hscard : s.card = 3) (htcard : t.card = 3)
    (hps : (p : E) ∈ s) (hpt : (p : E) ∈ t)
    (hu : u ∈ T.ambient.faces) (hv : v ∈ T.ambient.faces)
    (hucard : u.card = 4) (hvcard : v.card = 4) (hsu : s ⊆ u) (htv : t ⊆ v)
    (P Q : V2 →ᴬ[ℝ] E) (hPi : Function.Injective P) (hQi : Function.Injective Q)
    (hP : ∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x)
    (hQ : ∀ x ∈ convexHull ℝ (t : Set E), Q (T.inverse x) = x)
    {w z : E} (hw : w ∈ convexHull ℝ (u : Set E))
    (hz : z ∈ convexHull ℝ (v : Set E)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      (affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w) *
        affineDiskNormal (c.toAffineEquiv.toAffineMap.comp Q.toAffineMap) (c z)) * α =
      β * (((T.pairChart p).chart w).2 * ((T.pairChart p).chart z).2) := by
  classical
  let H := (T.pairChart p).chart
  obtain ⟨F, K, N, L, hFb, hK, hKcv, hpK, hKsource, hKaff, hKi,
    hN, hNcv, hpN, hL, hLs, hLcv, hLint, hLsource, hLaff, hLi⟩ :=
    T.exists_convex_chart_restrictions hb p c
  obtain ⟨A, B, hA, hAB⟩ :=
    T.exists_incident_affine_chart_formulas p c hs hscard hps hu hucard hsu P hPi hP
  obtain ⟨C, G, hC, hCG⟩ :=
    T.exists_incident_affine_chart_formulas p c ht htcard hpt hv hvcard htv Q hQi hQ
  have hambient_patch {r : Finset E} (hr : r ∈ T.ambient.faces)
      (hrcard : r.card = 4) (hpr : (p : E) ∈ r)
      (A0 : V ≃ᵃ[ℝ] V)
      (hA0 : ∀ x ∈ convexHull ℝ (r : Set E), A0 (c x) = diskChartCoordinates (H x)) :
      ∃ U : Set V, IsOpen U ∧ U.Nonempty ∧ U ⊆ K.space ∧
        EqOn A0 (fun x => diskChartCoordinates (H (c.symm x))) U := by
    let S : Set V := c '' (r : Set E)
    have hind := (T.ambient.indep hr).map' c.toAffineEquiv.toAffineMap c.injective
    have hrange : range (c.toAffineEquiv.toAffineMap ∘ ((↑) : r → E)) = S := by
      ext x
      simp only [S, mem_range, mem_image, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.property, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    have hspan : affineSpan ℝ S = ⊤ := by
      rw [← hrange]
      exact hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by simp [Module.finrank_prod, hrcard])
    have hphull : c p ∈ convexHull ℝ S := subset_convexHull ℝ _
      (mem_image_of_mem c hpr)
    have hne := open_meets_simplex_interior hspan isOpen_interior hphull hpK
    refine ⟨interior (convexHull ℝ S) ∩ interior K.space,
      isOpen_interior.inter isOpen_interior, hne,
      fun x hx => interior_subset hx.2, ?_⟩
    intro x hx
    have hx' : x ∈ c '' convexHull ℝ (r : Set E) := by
      change x ∈ c.toAffineEquiv.toAffineMap '' convexHull ℝ (r : Set E)
      rw [c.toAffineEquiv.toAffineMap.image_convexHull]
      exact interior_subset hx.1
    obtain ⟨y, hy, rfl⟩ := hx'
    simpa only [c.symm_apply_apply] using hA0 y hy
  have htangent_patch {r : Finset E} (hr : r ∈ T.disk.faces)
      (hrcard : r.card = 3) (hpr : (p : E) ∈ r)
      (P0 : V2 →ᴬ[ℝ] E)
      (hP0 : ∀ x ∈ convexHull ℝ (r : Set E), P0 (T.inverse x) = x)
      (A0 : V ≃ᵃ[ℝ] V) (B0 : V2 ≃ᵃ[ℝ] V2)
      (hA0 : ∀ x ∈ convexHull ℝ (r : Set E), A0 (c x) = diskChartCoordinates (H x))
      (hAB0 : ∀ x : V2, A0 (c (P0 x)) = (B0 x, 0)) :
      ∃ U : Set V2, IsOpen U ∧ U.Nonempty ∧ U ⊆ L.space ∧
        EqOn B0 (fun x => (diskChartCoordinates (H (F x))).1) U := by
    let S : Set V2 := T.inverse '' (r : Set E)
    have hspan := original_triangle_span T hr hrcard P0 hP0
    have hpS : T.inverse p ∈ convexHull ℝ S := subset_convexHull ℝ _
      (mem_image_of_mem T.inverse hpr)
    have hne := open_meets_simplex_interior hspan isOpen_interior hpS hpN
    obtain ⟨hCube, hval⟩ := original_triangle_values T hr P0 hP0 F hFb
    refine ⟨interior (convexHull ℝ S) ∩ interior N.space,
      isOpen_interior.inter isOpen_interior, hne, ?_, ?_⟩
    · intro x hx
      rw [hLs]
      exact ⟨interior_subset hx.2, hCube (interior_subset hx.1)⟩
    · intro x hx
      have hvalue := hval x (interior_subset hx.1)
      calc
        B0 x = (A0 (c (P0 x))).1 := (congrArg Prod.fst (hAB0 x)).symm
        _ = (diskChartCoordinates (H (P0 x))).1 := congrArg Prod.fst (hA0 _ hvalue.2)
        _ = (diskChartCoordinates (H (F x))).1 := by rw [hvalue.1]
  obtain ⟨UA, hUA, hUAne, hUAK, hUAeq⟩ := hambient_patch hu hucard (hsu hps) A hA
  obtain ⟨UC, hUC, hUCne, hUCK, hUCeq⟩ := hambient_patch hv hvcard (htv hpt) C hC
  obtain ⟨UB, hUB, hUBne, hUBL, hUBeq⟩ := htangent_patch hs hscard hps P hP A B
    (fun x hx => hA x (convexHull_mono hsu hx)) hAB
  obtain ⟨UG, hUG, hUGne, hUGL, hUGeq⟩ := htangent_patch ht htcard hpt Q hQ C G
    (fun x hx => hC x (convexHull_mono htv hx)) hCG
  have hdetA := det_mul_pos_of_actual_convex_affine_patches K hK
    (by simp [Module.finrank_prod]) hKcv ⟨c p, hpK⟩ hKaff hKi
    hUA hUAne hUAK hUC hUCne hUCK A C hUAeq hUCeq
  have hdetB := det_mul_pos_of_actual_convex_affine_patches L hL
    (by simp) hLcv hLint hLaff hLi
    hUB hUBne hUBL hUG hUGne hUGL B G hUBeq hUGeq
  have h1 := affineDiskNormal_mul_ambient_det
    (c.toAffineEquiv.toAffineMap.comp P.toAffineMap)
    A B hAB (c w)
  have h2 := affineDiskNormal_mul_ambient_det
    (c.toAffineEquiv.toAffineMap.comp Q.toAffineMap)
    C G hCG (c z)
  refine ⟨_, _, hdetA, hdetB, ?_⟩
  calc
    _ = (affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w) *
        LinearMap.det (A.linear : V →ₗ[ℝ] V)) *
      (affineDiskNormal (c.toAffineEquiv.toAffineMap.comp Q.toAffineMap) (c z) *
        LinearMap.det (C.linear : V →ₗ[ℝ] V)) := by ring
    _ = (LinearMap.det (B.linear : V2 →ₗ[ℝ] V2) *
        LinearMap.det (G.linear : V2 →ₗ[ℝ] V2)) * ((A (c w)).2 * (C (c z)).2) := by
      rw [h1, h2]
      ring
    _ = _ := by rw [hA w hw, hC z hz]; rfl

theorem HamiltonProperDiskTriangulation.normal_mul_pos_at_vertex
    (T : HamiltonProperDiskTriangulation R D b) (hb : b.IsFinitePL)
    (p : T.disk.vertices) (c : E ≃ᴬ[ℝ] V)
    {s t u v : Finset E} (hs : s ∈ T.disk.faces) (ht : t ∈ T.disk.faces)
    (hscard : s.card = 3) (htcard : t.card = 3)
    (hps : (p : E) ∈ s) (hpt : (p : E) ∈ t)
    (hu : u ∈ T.ambient.faces) (hv : v ∈ T.ambient.faces)
    (hucard : u.card = 4) (hvcard : v.card = 4) (hsu : s ⊆ u) (htv : t ⊆ v)
    (P Q : V2 →ᴬ[ℝ] E) (hPi : Function.Injective P) (hQi : Function.Injective Q)
    (hP : ∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x)
    (hQ : ∀ x ∈ convexHull ℝ (t : Set E), Q (T.inverse x) = x)
    {w z : E} (hw : w ∈ convexHull ℝ (u : Set E))
    (hz : z ∈ convexHull ℝ (v : Set E))
    (hside : 0 < ((T.pairChart p).chart w).2 * ((T.pairChart p).chart z).2) :
    0 < affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w) *
      affineDiskNormal (c.toAffineEquiv.toAffineMap.comp Q.toAffineMap) (c z) := by
  obtain ⟨α, β, hα, hβ, he⟩ := T.normal_product_equation_at_vertex hb p c
    hs ht hscard htcard hps hpt hu hv hucard hvcard hsu htv P Q hPi hQi hP hQ hw hz
  apply (mul_pos_iff_of_pos_right hα).mp
  rw [he]
  exact mul_pos hβ hside

end PoincareConjecture.M76.HamiltonIndexOne
