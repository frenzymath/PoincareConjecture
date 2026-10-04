import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskNormalComparison

/-!
# Sign comparison for the retained chart pieces

Actual tetrahedral and tangential formulas may come from a refinement
different from the convex-box triangulation. Agreement on a nonempty
open patch identifies them with full pieces of that triangulation.
This preserves the actual formulas and gives the comparison used in
the coherent normal labels. See derivation351b.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.HamiltonIndexOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem affine_patch_eq_full_piece
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {f : E → E}
    (pieces : {s : Finset E // s ∈ K.faces ∧ s.card = Module.finrank ℝ E + 1} → E ≃ᵃ[ℝ] E)
    (hpieces : ∀ s, EqOn (pieces s) f (convexHull ℝ (s.val : Set E)))
    {V : Set E} (hV : IsOpen V) (hne : V.Nonempty) (hVK : V ⊆ K.space)
    (a : E ≃ᵃ[ℝ] E) (ha : EqOn a f V) : ∃ s, a = pieces s := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, hs, hcard, hxs⟩ := K.exists_full_face_of_mem_interior hK
    (hV.subset_interior_iff.mpr hVK hx)
  have hint : (interior (convexHull ℝ (s : Set E))).Nonempty := by
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    simpa using ((K.indep hs).affineBasisOfCard hcard).tot
  have hxcl : x ∈ closure (interior (convexHull ℝ (s : Set E))) := by
    rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hxs
  obtain ⟨y, hyV, hyint⟩ := mem_closure_iff.mp hxcl V hV hx
  have hW : IsOpen (V ∩ interior (convexHull ℝ (s : Set E))) := hV.inter isOpen_interior
  have hWne : (V ∩ interior (convexHull ℝ (s : Set E))).Nonempty := ⟨y, hyV, hyint⟩
  refine ⟨⟨s, hs, hcard⟩, AffineEquiv.toAffineMap_injective ?_⟩
  apply AffineMap.ext_on (hW.affineSpan_eq_top hWne)
  intro z hz
  exact (ha hz.1).trans ((hpieces ⟨s, hs, hcard⟩) (interior_subset hz.2)).symm

/-- Any two actual affine chart formulas on nonempty open patches
of a convex injective PL map have the same determinant sign. The
pieces need not use its supplied triangulation. See351b. -/
theorem det_mul_pos_of_actual_convex_affine_patches
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : 0 < Module.finrank ℝ E)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    {f : E → E} (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    {V W : Set E} (hV : IsOpen V) (hVne : V.Nonempty) (hVK : V ⊆ K.space)
    (hW : IsOpen W) (hWne : W.Nonempty) (hWK : W ⊆ K.space)
    (a b : E ≃ᵃ[ℝ] E) (ha : EqOn a f V) (hb : EqOn b f W) :
    0 < LinearMap.det (a.linear : E →ₗ[ℝ] E) *
      LinearMap.det (b.linear : E →ₗ[ℝ] E) := by
  obtain ⟨pieces, hpieces, hsign⟩ :=
    exists_actual_convex_affine_pieces_with_same_sign K hK hdim hcv hne hf hinj
  obtain ⟨s, rfl⟩ := affine_patch_eq_full_piece K hK pieces hpieces hV hVne hVK a ha
  obtain ⟨t, rfl⟩ := affine_patch_eq_full_piece K hK pieces hpieces hW hWne hWK b hb
  exact hsign s t

/-- The actual full-dimensional and planar chart maps compare
two retained original disk normals on the same strict local side.
Both sign premises are constructed from finite PL maps and carrier
injection inside this theorem. See derivation351b. -/
theorem normal_mul_pos_of_actual_chart_patches
    (K : SimplicialComplex ℝ (E × ℝ)) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hdim : 0 < Module.finrank ℝ E)
    (hKcv : Convex ℝ K.space) (hKne : (interior K.space).Nonempty)
    (hLcv : Convex ℝ L.space) (hLne : (interior L.space).Nonempty)
    {f : (E × ℝ) → (E × ℝ)} (hf : K.AffineOnFaces f) (hfi : InjOn f K.space)
    {g : E → E} (hg : L.AffineOnFaces g) (hgi : InjOn g L.space)
    {V W : Set (E × ℝ)} (hV : IsOpen V) (hVne : V.Nonempty) (hVK : V ⊆ K.space)
    (hW : IsOpen W) (hWne : W.Nonempty) (hWK : W ⊆ K.space)
    {U Z : Set E} (hU : IsOpen U) (hUne : U.Nonempty) (hUL : U ⊆ L.space)
    (hZ : IsOpen Z) (hZne : Z.Nonempty) (hZL : Z ⊆ L.space)
    (A C : (E × ℝ) ≃ᵃ[ℝ] (E × ℝ)) (B D : E ≃ᵃ[ℝ] E)
    (hA : EqOn A f V) (hC : EqOn C f W)
    (hB : EqOn B g U) (hD : EqOn D g Z)
    (P Q : E →ᵃ[ℝ] (E × ℝ))
    (hP : ∀ x : E, A (x, 0) = P (B x))
    (hQ : ∀ x : E, C (x, 0) = Q (D x))
    (p q : E × ℝ) (hside : 0 < p.2 * q.2) :
    0 < affineDiskNormal P (A p) * affineDiskNormal Q (C q) := by
  have hprod : 0 < Module.finrank ℝ (E × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  exact affineDiskNormal_mul_pos_of_piece_signs P Q A C B D hP hQ
    (det_mul_pos_of_actual_convex_affine_patches K hK hprod hKcv hKne hf hfi
      hV hVne hVK hW hWne hWK A C hA hC)
    (det_mul_pos_of_actual_convex_affine_patches L hL hdim hLcv hLne hg hgi
      hU hUne hUL hZ hZne hZL B D hB hD) p q hside

end PoincareMT.M76.HamiltonIndexOne
