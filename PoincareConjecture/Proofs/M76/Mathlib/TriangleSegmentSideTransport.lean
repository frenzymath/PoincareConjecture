import PoincareConjecture.Proofs.M76.Mathlib.ConvexIntrinsicInterior
import PoincareConjecture.Proofs.M76.Mathlib.AffinePlaneGermRigidity
import PoincareConjecture.Proofs.M76.Mathlib.PlanarRegionSideTransport

set_option autoImplicit false

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Continuous.exists_uniform_segments_in_open
    {u v : ℝ → E} (hu : Continuous u) (hv : Continuous v)
    {U : Set E} (hU : IsOpen U) (hseg : segment ℝ (u 0) (v 0) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, |z| < δ → segment ℝ (u z) (v z) ⊆ U := by
  let F : ℝ × ℝ → E := fun w => (1 - w.2) • u w.1 + w.2 • v w.1
  have hF : Continuous F :=
    ((continuous_const.sub continuous_snd).smul (hu.comp continuous_fst)).add
      (continuous_snd.smul (hv.comp continuous_fst))
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : F (0, t) ∈ U := by
    apply hseg
    rw [segment_eq_image]
    exact ⟨t, ht, rfl⟩
  have hevent : ∀ᶠ z : ℝ in 𝓝 0, ∀ t ∈ Icc (0 : ℝ) 1, F (z, t) ∈ U :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun t ht => (hU.preimage hF).mem_nhds (hzero t ht))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz
  rw [segment_eq_image]
  rintro _ ⟨t, ht, rfl⟩
  exact hball hzball t ht

namespace Geometry.SimplicialComplex

theorem exists_open_triangle_plane_neighborhood_of_segment
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (C : E →ₗ[ℝ] ℝ)
    (hplane : ∀ x : E, x ∈ affineSpan ℝ (s : Set E) ↔ C x = 0) :
    ∃ U : Set E, IsOpen U ∧ segment ℝ a p ⊆ U ∧
      ∀ x ∈ U, x ∈ K.space ↔ C x = 0 := by
  have hseg : segment ℝ a p ⊆ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior.segment_subset ha hp
  have hlocal (x : segment ℝ a p) :=
    K.exists_open_eq_affineSpan_of_triangle_interior hK hbound hs hcard (hseg x.property)
  choose U hU hxU hKU using hlocal
  refine ⟨⋃ x, U x, isOpen_iUnion hU, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := mem_iUnion.mp hx
    exact (show x ∈ K.space ↔ x ∈ affineSpan ℝ (s : Set E) from
      ⟨fun h => ((hKU y).subset ⟨h, hxy⟩).1,
        fun h => ((hKU y).symm.subset ⟨h, hxy⟩).1⟩).trans (hplane x)

theorem exists_uniform_transverse_segments_avoiding_carrier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (u v : ℝ → E) (hu : Continuous u) (hv : Continuous v)
    (hu0 : u 0 ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hv0 : v 0 ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (C : E →ₗ[ℝ] ℝ)
    (hplane : ∀ x : E, x ∈ affineSpan ℝ (s : Set E) ↔ C x = 0)
    (huC : ∀ z, C (u z) = z) (hvC : ∀ z, C (v z) = z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, |z| < δ → z ≠ 0 →
      Disjoint (segment ℝ (u z) (v z)) K.space := by
  obtain ⟨U, hU, hseg, hKU⟩ :=
    K.exists_open_triangle_plane_neighborhood_of_segment hK hbound hs hcard hu0 hv0 C hplane
  obtain ⟨δ, hδ, hsegments⟩ := hu.exists_uniform_segments_in_open hv hU hseg
  refine ⟨δ, hδ, ?_⟩
  intro z hz hz0
  apply disjoint_left.mpr
  intro x hx hxK
  have hxC : C x = 0 := (hKU x (hsegments z hz hx)).mp hxK
  obtain ⟨a, b, _, _, hab, rfl⟩ := hx
  have heq : C (a • u z + b • v z) = z := by
    rw [map_add, map_smul, map_smul, huC, hvC, smul_eq_mul, smul_eq_mul,
      ← add_mul, hab, one_mul]
  exact hz0 (heq.symm.trans hxC)

variable [FiniteDimensional ℝ E]

theorem exists_uniform_planar_disk_side_transport
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (u v : ℝ → E) (hu : Continuous u) (hv : Continuous v)
    (hu0 : u 0 ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hv0 : v 0 ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (C : E →ₗ[ℝ] ℝ)
    (hplane : ∀ x : E, x ∈ affineSpan ℝ (s : Set E) ↔ C x = 0)
    (huC : ∀ z, C (u z) = z) (hvC : ∀ z, C (v z) = z)
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hdplane : d ⊆ {x | A x = 0}) (hqK : q ⊆ K.space)
    (huA : ∀ z, A (u z) = 0) (hvA : ∀ z, A (v z) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, |z| < δ → z ≠ 0 → (u z ∈ d ↔ v z ∈ d) := by
  obtain ⟨δ, hδ, havoid⟩ :=
    K.exists_uniform_transverse_segments_avoiding_carrier hK hbound hs hcard
      u v hu hv hu0 hv0 C hplane huC hvC
  refine ⟨δ, hδ, ?_⟩
  intro z hz hz0
  apply hd.mem_iff_of_preconnected_avoiding_rim_in_plane A hA hdim hdplane
    (convex_segment (𝕜 := ℝ) (u z) (v z)).isPreconnected
    (((convex_singleton (0 : ℝ)).affine_preimage A).segment_subset (huA z) (hvA z))
    ((havoid z hz hz0).mono_right hqK)
    (left_mem_segment ℝ (u z) (v z)) (right_mem_segment ℝ (u z) (v z))

end Geometry.SimplicialComplex
