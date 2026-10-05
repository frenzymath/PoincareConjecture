import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialGenerators

/-!+# Finite local patches in geometric complexes

A neighborhood meeting only finitely many closed faces supplies
a finite subcomplex around a carrier-interior point. Face-affine
maps on such complexes satisfy the local PL coordinate property.
See Hudson 1969, pp. 3--5, 15--19, Hamilton 1976, pp. 68--69
and M76 derivation 83.
-/

set_option autoImplicit false

open Set Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A carrier-interior point with only finitely many incident
faces in a neighborhood has a finite subcomplex neighborhood.
See Hudson pp. 3--5, Hamilton pp. 68--69 and M76 derivation 83. -/
theorem exists_finite_subcomplex_neighborhood (K : SimplicialComplex ℝ E)
    {x : E} (hx : x ∈ interior K.space)
    (hlocal : ∃ U ∈ 𝓝 x,
      {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}.Finite) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L ≤ K ∧ x ∈ interior L.space := by
  obtain ⟨U, hxU, hfinite⟩ := hlocal
  let A : Set (Finset E) :=
    Subtype.val '' {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}
  have hA : A.Finite := hfinite.image _
  have hAK : A ⊆ K.faces := by
    rintro _ ⟨s, _, rfl⟩
    exact s.property
  have hind (s : Finset E) (hs : s ∈ A) := K.indep (hAK hs)
  have hinter (s : Finset E) (hs : s ∈ A) (t : Finset E) (ht : t ∈ A) :=
    K.inter_subset_convexHull (hAK hs) (hAK ht)
  let L := ofGenerators A hind hinter
  have hLK : L ≤ K := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K.down_closed (hAK ht) hst hs
  refine ⟨L, finite_ofGenerators_faces hA hind hinter, hLK, ?_⟩
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset
    (Filter.inter_mem (mem_interior_iff_mem_nhds.mp hx) hxU)
  rintro y ⟨hyK, hyU⟩
  obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hyK
  have hsA : s ∈ A := ⟨⟨s, hs⟩, ⟨y, hys, hyU⟩, rfl⟩
  exact L.convexHull_subset_space
    ⟨K.nonempty_of_mem_faces hs, s, hsA, Finset.Subset.refl s⟩ hys

variable [FiniteDimensional ℝ E] {K : SimplicialComplex ℝ E} {f : E → F}

/-- Local finiteness at carrier-interior points is enough for
a face-affine map to be locally PL on that interior. Accumulation
outside the carrier is allowed. See Hudson pp. 15--19 and
M76 derivation 83. -/
theorem AffineOnFaces.locallyPiecewiseAffineOn_of_local_faces
    (hf : K.AffineOnFaces f)
    (hlocal : ∀ x ∈ interior K.space, ∃ U ∈ 𝓝 x,
      {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}.Finite) :
    LocallyPiecewiseAffineOn f (interior K.space) := by
  intro x hx
  obtain ⟨L, hL, hLK, hxL⟩ := K.exists_finite_subcomplex_neighborhood hx (hlocal x hx)
  have hfL : L.AffineOnFaces f := fun s hs => hf s (hLK hs)
  obtain ⟨R, hR, hxR, hRK, hfR⟩ := hfL.exists_finite_neighborhood hL
    isCompact_singleton isOpen_interior (singleton_subset_iff.mpr ⟨hxL, hx⟩)
  exact ⟨R, hR, hxR (mem_singleton x), fun _ hy => (hRK hy).2, hfR⟩

/-- Affine formulas on an ambient locally finite complex give
the standard local PL map property on its carrier interior.
See Hudson pp. 15--19 and M76 derivation 83. -/
theorem AffineOnFaces.locallyPiecewiseAffineOn_of_locallyFinite
    (hf : K.AffineOnFaces f)
    (hlocal : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E))) :
    LocallyPiecewiseAffineOn f (interior K.space) :=
  hf.locallyPiecewiseAffineOn_of_local_faces fun x _ => hlocal x

end Geometry.SimplicialComplex
