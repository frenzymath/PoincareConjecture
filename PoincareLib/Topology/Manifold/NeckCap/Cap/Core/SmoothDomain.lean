import PoincareLib.Topology.Manifold.NeckCap.Cap.Core.Charts
import PoincareLib.Topology.Manifold.NeckCap.Cap.CoreConnected
import PoincareLib.Geometry.Manifold.SmoothDomain.Embedding
import PoincareLib.Geometry.Manifold.SmoothDomain.Interior

/-!
# The smooth domain structure on a cap core

The regular defining functions in a cap certificate give smooth half-space
charts on its specified compact core. The resulting inclusion is a smooth
embedding, and its intrinsic boundary has image the given boundary sphere.

Reference: Morgan--Tian, Definition 9.72, pp. 230--231, and
Proposition A.21, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)

/-- The specified open core of every cap is a compactly contained smooth
domain, with a smoothly embedded manifold-with-boundary closure. -/
theorem nonempty_smoothDomain_core :
    Nonempty (Poincare.Manifold.SmoothDomain 3 C.core) := by
  have hcharts : ∀ a : closure C.core,
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
        (a : M) ∈ e.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
        e.IsImage (closure C.core) {y | 0 ≤ y 0} := by
    intro a
    simpa only [C.closure_core_eq_closed_core] using
      C.exists_closed_core_halfspace_chart
        ⟨a.val, C.closure_core_eq_closed_core ▸ a.property⟩
  choose amb hamb using hcharts
  obtain ⟨CS, rel, hsource, _, hman, hemb⟩ :=
    Poincare.Manifold.exists_smooth_embedding_of_halfspace_charts
      (n := 2) (by simp) (closure C.core) amb hamb
  let := CS
  let := hman
  have hinterior : Subtype.val '' (𝓡∂ 3).interior (closure C.core) = C.core := by
    rw [Poincare.Manifold.image_interior_of_isSmoothEmbedding hemb,
      C.closure_core_eq_closed_core, ← C.core_eq_interior_closed_core]
  have hboundary : Subtype.val '' (𝓡∂ 3).boundary (closure C.core) =
      C.boundary_sphere := by
    rw [← ModelWithCorners.compl_interior, compl_eq_univ_sdiff,
      image_sdiff Subtype.val_injective, image_univ, Subtype.range_val,
      hinterior, C.closure_core_eq_closed_core, ← C.boundary_eq_closed_core_diff_core]
  have hb : ((𝓡∂ 3).boundary (closure C.core)).Nonempty := by
    apply Set.Nonempty.of_image (f := Subtype.val)
    rw [hboundary, C.boundary_eq_neck_sphere]
    exact ⟨C.boundary_neck.center, C.boundary_neck.center_on_central_sphere⟩
  exact ⟨{
    isOpen := C.isOpen_core
    isConnected := C.isConnected_core
    isCompact_closure := C.closure_core_eq_closed_core.symm ▸ C.closed_core_compact
    chartedSpace := CS
    isManifold := hman
    isSmoothEmbedding := hemb
    image_interior := hinterior
    boundary_nonempty := hb }⟩

/-- Any smooth-domain structure on the cap core has the specified sphere as
the image of its intrinsic boundary. -/
theorem smoothDomain_image_boundary (D : Poincare.Manifold.SmoothDomain 3 C.core) :
    Subtype.val '' D.intrinsicBoundary = C.boundary_sphere := by
  rw [D.image_boundary, C.frontier_core_eq_boundary]

end PoincareMT.CapCertificate
