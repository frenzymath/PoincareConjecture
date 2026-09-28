import PoincareConjecture.Proofs.M76.Triangulation.ThreeDimensionalSliceDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace Set

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

theorem IsConnected.eq_member_of_finite_disjoint_closed_cover {S : Set X}
    (hS : IsConnected S) (D : ι → Set X) (hD : ∀ i, IsClosed (D i))
    (hdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hcover : S = ⋃ i, D i) : ∃ i, S = D i := by
  classical
  obtain ⟨x, hxS⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ hxS)
  let R : Set X := ⋃ j : {j : ι // j ≠ i}, D j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hD j)
  have hinter : D i ∩ R = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyi, hyR⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyR
    exact Set.disjoint_left.mp (hdisj (Ne.symm j.property)) hyi hyj
  have hsub : S ⊆ D i ∪ R := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover ▸ hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hS.isPreconnected
    (D i) R (hD i) hR hsub (by rw [hinter, inter_empty])
  have hleft : S ⊆ D i := hside.resolve_right (fun h => by
    have hx : x ∈ D i ∩ R := ⟨hxi, h hxS⟩
    rw [hinter] at hx
    exact hx)
  refine ⟨i, Subset.antisymm hleft ?_⟩
  intro y hy
  rw [hcover]
  exact mem_iUnion.mpr ⟨i, hy⟩

end Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finitePL_disk_of_connected_regularSlice (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 3) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hconn : IsConnected (K.space ∩ {x | A x = 0})) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (K.space ∩ {x | A x = 0}) ∧
      D ⊆ {x | A x = 0} ∧ D ∩ K.space = K.space ∩ {x | A x = 0} := by
  classical
  obtain ⟨a, r, hleft, hright, ha⟩ := A.exists_zeroLevel_coordinates
    (K.linear_ne_zero_of_nonempty_regularSlice A hreg hconn.nonempty)
    (F := ℝ × ℝ) (by simp [hdim, Module.finrank_prod])
  obtain ⟨n, Q, hQ, hcover, hdisj⟩ := K.exists_regularSlice_plane_polygons
    A hK hreg hpure hcofaces a r hleft hright ha
  have hproj : a ⁻¹' K.space = r '' (K.space ∩ {x | A x = 0}) := by
    ext y
    constructor
    · intro hy
      exact ⟨a y, ⟨hy, ha y⟩, hleft y⟩
    · rintro ⟨x, hx, rfl⟩
      change a (r x) ∈ K.space
      rw [hright hx.2]
      exact hx.1
  have hplane : IsConnected (a ⁻¹' K.space) := by
    rw [hproj]
    exact hconn.image r r.continuous.continuousOn
  let := K.finite_regularSliceGraph_components A hK
  obtain ⟨i, hi⟩ := hplane.eq_member_of_finite_disjoint_closed_cover
    (fun i => (Q i).boundary ℝ) (fun i => (Q i).isClosed_boundary) hdisj hcover
  have hboundary : a '' (Q i).boundary ℝ = K.space ∩ {x | A x = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hi.symm.subset hy, ha y⟩
    · intro hx
      refine ⟨r x, ?_, hright hx.2⟩
      rw [← hi]
      change a (r x) ∈ K.space
      rw [hright hx.2]
      exact hx.1
  have hdisk := ((Q i).isFinitePLBallPair_closed_inside (hQ i).2 (hQ i).1).affine_image
    a hleft.injective.injOn
  rw [hboundary] at hdisk
  refine ⟨a '' closure (Q i).inside, hdisk, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact ha y
  · apply Subset.antisymm
    · rintro x ⟨⟨y, _, rfl⟩, hxK⟩
      exact ⟨hxK, ha y⟩
    · intro x hx
      exact ⟨hdisk.1 hx, hx.1⟩

end Geometry.SimplicialComplex
