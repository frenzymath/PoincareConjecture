import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Finite.LoopValueNet
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Uniform.CloseLoopAnnuli
import PoincareLib.Geometry.CurveShortening.Comparison.Theory

/-!
# Finite small-annulus nets for every raw compact family

The chosen parameter node works for every positive circumference below one
common cutoff. All annuli lie in the geometry's actual chosen product.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Construct finite small-annulus nets with nodes chosen before every sufficiently small
circle circumference. Source: Auxiliary step for MT Section 19.6, pp. 461-462; project
construction in `proof-work/tasks/M64/reports/2026-09-24-finite-nets-closed.md`. -/
theorem m64FamilyAnnulusNets_of_compact
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
    (G : M63AmbientGeometry F) (hcompact : IsCompact (univ : Set M)) :
    M64FamilyAnnulusNets G := by
  intro Gamma mu hmu
  let e : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  let : CompactSpace LoopTwoSphere := e.compactSpace
  obtain ⟨epsilon, hepsilon, hannuli⟩ :=
    m64_uniform_close_loop_canonical_annuli F a hcompact Gamma Gamma.continuous hmu
  obtain ⟨k, nodes, hnodes⟩ :=
    m64_finite_loop_value_net (F.metric a) Gamma Gamma.continuous hepsilon
  refine ⟨{
    node_count := k
    nodes := nodes
    circumference_cutoff := curvePeriod
    cutoff_positive := Real.two_pi_pos
    covers := ?_ }⟩
  intro z
  obtain ⟨i, hi⟩ := hnodes z
  exact ⟨i, fun circumference h hc =>
    hannuli z (nodes i) hi circumference (G.product circumference h) hc.le⟩

end PoincareMT
