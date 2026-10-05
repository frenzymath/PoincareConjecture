import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.RegularSliceDisk
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHyperplaneCoordinates

/-!
# An innermost disk in a three-dimensional surface slice

The affine plane coordinates required by the regular-slice disk
construction follow from the ambient dimension. Regularity and
nonemptiness rule out constant heights. See Alexander 1924,
pp. 6--7, Hamilton 1976, p. 66 and M76 derivation 124.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A nonempty vertex-regular slice has a nonconstant affine
height, even without surface hypotheses. See derivation 124. -/
theorem linear_ne_zero_of_nonempty_regularSlice (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hne : (K.space ∩ {x | A x = 0}).Nonempty) : A.linear ≠ 0 := by
  classical
  intro hA
  obtain ⟨x, hxK, hxA⟩ := hne
  change A x = 0 at hxA
  obtain ⟨s, hs, _⟩ := mem_space_iff.mp hxK
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvK : v ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  apply hreg v hvK
  have h := A.linearMap_vsub v x
  simpa [hA, hxA] using h.symm

/-- Every nonempty regular section of a finite pure closed
triangulated surface in three-space contains a finite PL disk
meeting the entire surface exactly in its polygonal boundary.
No plane parametrization is assumed. See Alexander pp. 6--7
and M76 derivation 124. -/
theorem exists_finitePL_disk_in_regularSlice (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 3) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hne : (K.space ∩ {x | A x = 0}).Nonempty) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)) (D : Set E),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      D ⊆ {x | A x = 0} ∧ D ∩ K.space = P.boundary ℝ ∧
      Disjoint (D \ P.boundary ℝ) K.space := by
  obtain ⟨a, r, hleft, hright, ha⟩ := A.exists_zeroLevel_coordinates
    (K.linear_ne_zero_of_nonempty_regularSlice A hreg hne)
    (F := ℝ × ℝ) (by simp [hdim, Module.finrank_prod])
  exact K.exists_regularSlice_finitePL_disk A hK hreg hpure hcofaces
    a r hleft hright ha hne

end Geometry.SimplicialComplex
