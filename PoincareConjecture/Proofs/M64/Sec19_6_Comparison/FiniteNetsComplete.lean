import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.FiniteLoopValueNet
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.UniformCloseLoopAnnuli
import PoincareConjecture.Statements.M64Comparison










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




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

end PoincareConjecture
