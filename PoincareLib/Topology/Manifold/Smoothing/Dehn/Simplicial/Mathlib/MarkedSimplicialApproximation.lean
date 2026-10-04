import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.CarrierSimplicialApproximation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedronNeighborhoodRetraction
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Actual finite PL pair approximation in an open boundary mark

An actual fine target subdivision retains the whole marked polyhedron
by explicit subpolyhedron alignment. The carrier approximation then
keeps every straight boundary track in the original open mark.
See Hatcher, Theorem 3.1, p. 45, and the precise PL reconstruction in
Dehn derivations 022 section 3 and 023 sections 2--3.
-/

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- A continuous finite polyhedral pair has an actual finite PL
approximation whose entire straight homotopy stays in the target,
and whose whole marked-source tracks stay in the original relatively
open target mark. No PL source-boundary premise is used.
See Dehn derivation 023, sections 2--3. -/
theorem exists_marked_finitePL_approximation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (P Z : SimplicialComplex ℝ G) (hP : P.faces.Finite) (hZP : Z ≤ P)
    (f : C(K.space, P.space)) (B : Set K.space) (hB : IsCompact B)
    (O : Set G) (hO : IsOpen ((Subtype.val : Z.space → G) ⁻¹' O))
    (hBO : MapsTo (fun x : K.space => (f x : G)) B (O ∩ Z.space)) :
    ∃ g : E → G, FinitePiecewiseAffineOn g K.space ∧
      (∀ x : K.space, segment ℝ (f x : G) (g x) ⊆ P.space) ∧
      ∀ x ∈ B, segment ℝ (f x : G) (g x) ⊆ O ∩ Z.space := by
  classical
  obtain ⟨U, hU, hUO⟩ := isOpen_induced_iff.mp hO
  have himage : IsCompact ((fun x : K.space => (f x : G)) '' B) :=
    hB.image (continuous_subtype_val.comp f.continuous)
  have himageU : (fun x : K.space => (f x : G)) '' B ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    have h : (⟨(f x : G), (hBO hx).2⟩ : Z.space) ∈
        (Subtype.val : Z.space → G) ⁻¹' O := (hBO hx).1
    rw [← hUO] at h
    exact h
  obtain ⟨rho, hrho, hrhoU⟩ := himage.exists_thickening_subset_open hU himageU
  let n := hP.toFinset.sup Finset.card
  have hn (s : Finset G) (hs : s ∈ P.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hP.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨P₀, hP₀, hP₀P, _, hmesh⟩ :=
    P.exists_finite_subdivision_mesh hP hn (half_pos hrho)
  have hZP₀ : Z.space ⊆ P₀.space := fun _ hx =>
    hP₀P.space_eq.symm.subset (space_subset_of_le hZP hx)
  obtain ⟨R, Z', hR, hRP₀, hZ'R, hZ'⟩ :=
    P₀.exists_subdivision_with_polyhedron_subcomplex Z hP₀ (hP.subset hZP) hZP₀
  have hRP : R.IsSubdivision P := hRP₀.trans hP₀P
  have hdiam (t : Finset G) (ht : t ∈ R.faces) :
      diam (convexHull ℝ (t : Set G)) ≤ rho / 2 := by
    obtain ⟨s, hs, hts⟩ := hRP₀.face_subset t ht
    exact (diam_mono hts (s.finite_toSet.isCompact_convexHull ℝ).isBounded).trans (hmesh s hs)
  let fR : C(K.space, R.space) :=
    ⟨fun x => ⟨(f x : G), hRP.space_eq.symm.subset (f x).property⟩,
      (continuous_subtype_val.comp f.continuous).subtype_mk _⟩
  obtain ⟨g, L, hL, hLK, hg, hcarrier⟩ :=
    K.exists_carrier_simplicial_approximation hK R hR fR
  refine ⟨g, ⟨L, hL, hLK.space_eq, hg⟩, ?_, ?_⟩
  · intro x
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp (fR x).property
    have hgt := hcarrier x t ht hxt
    exact ((convex_convexHull ℝ (t : Set G)).segment_subset hxt hgt).trans
      (fun _ hy => hRP.space_eq.subset (R.convexHull_subset_space ht hy))
  · intro x hx y hy
    have hxZ' : (fR x : G) ∈ Z'.space := by
      rw [hZ']
      exact (hBO hx).2
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxZ'
    have hgt := hcarrier x t (hZ'R ht) hxt
    have hyt : y ∈ convexHull ℝ (t : Set G) :=
      (convex_convexHull ℝ (t : Set G)).segment_subset hxt hgt hy
    have hyZ : y ∈ Z.space := hZ'.subset (Z'.convexHull_subset_space ht hyt)
    have hdist : dist y (f x : G) < rho :=
      ((dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded hyt hxt).trans
        (hdiam t (hZ'R ht))).trans_lt (half_lt_self hrho)
    have hyU : y ∈ U := hrhoU (mem_thickening_iff.mpr
      ⟨(f x : G), mem_image_of_mem (fun x : K.space => (f x : G)) hx, hdist⟩)
    have hyO : (⟨y, hyZ⟩ : Z.space) ∈ (Subtype.val : Z.space → G) ⁻¹' O := by
      rw [← hUO]
      exact hyU
    exact ⟨hyO, hyZ⟩

end Geometry.SimplicialComplex
