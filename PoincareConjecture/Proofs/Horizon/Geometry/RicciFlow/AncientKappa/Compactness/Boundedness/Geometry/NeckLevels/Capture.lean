import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Graph
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

theorem exists_regularLevel_component_parametrization
    (N : EpsilonNeck g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0)
    {W m c : ℝ} (hW : 0 < W) (hWdom : W < N.epsilon⁻¹) (hm : 0 < m)
    (hU : N.region (-W) W ⊆ U)
    (hderiv : ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (-W) W →
      m ≤ |deriv (fun s : ℝ => f (N.coordinate_map (q, s))) t|)
    (hcenter : ∀ q : UnitTwoSphere, |f (N.coordinate_map (q, 0)) - c| < m * W) :
    letI := openLevelSetChartedSpace hf U hreg 2 c
    letI := isManifold_openLevelSet hf U hreg 2 c
    ∃ (h : UnitTwoSphere → ℝ) (F : UnitTwoSphere → openLevelSet f U c),
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ q, h q ∈ Ioo (-W) W) ∧
      (∀ q, openLevelIncl f U c (F q) = N.coordinate_map (q, h q)) ∧
      ContMDiff (𝓡 2) (𝓡 2) ∞ F ∧
      (range F = {z | openLevelIncl f U c z ∈ N.region (-W) W}) ∧
      ∀ q, range F = connectedComponent (F q) := by
  letI := openLevelSetChartedSpace hf U hreg 2 c
  letI := isManifold_openLevelSet hf U hreg 2 c
  obtain ⟨h, hh, hheight, hlevel, hsmooth, hgraph⟩ :=
    N.exists_smooth_level_graph hf hW hWdom hm hderiv hcenter
  have hmem (q : UnitTwoSphere) : N.coordinate_map (q, h q) ∈ N.region (-W) W :=
    ((Set.ext_iff.mp hgraph) _).mpr (mem_range_self q) |>.1
  let F : UnitTwoSphere → openLevelSet f U c :=
    fun q => ⟨⟨N.coordinate_map (q, h q), hU (hmem q)⟩, hlevel q⟩
  have hFsmooth : ContMDiff (𝓡 2) (𝓡 2) ∞ F := by
    intro q
    exact (contMDiffAt_into_openLevelSet_iff hf 2 c U hreg F q).mpr (hsmooth q)
  have hrange : range F = {z | openLevelIncl f U c z ∈ N.region (-W) W} := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact hmem q
    · intro hz
      have hm : openLevelIncl f U c z ∈ range (fun q => N.coordinate_map (q, h q)) := by
        rw [← hgraph]
        exact ⟨hz, z.2⟩
      obtain ⟨q, hq⟩ := hm
      refine ⟨q, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hq
  have hopen : IsOpen (range F) := by
    rw [hrange]
    exact (N.isOpen_region (-W) W).preimage
      (contMDiff_openLevelIncl hf U hreg 2 c).continuous
  have hcompact : IsCompact (range F) := isCompact_range hFsmooth.continuous
  have hconnected : IsConnected (range F) := isConnected_range hFsmooth.continuous
  refine ⟨h, F, hh, hheight, fun _ => rfl, hFsmooth, hrange, ?_⟩
  intro q
  apply Subset.antisymm
  · exact hconnected.isPreconnected.subset_connectedComponent (mem_range_self q)
  · exact (show IsClopen (range F) from ⟨hcompact.isClosed, hopen⟩).connectedComponent_subset
      (mem_range_self q)

end PoincareConjecture.EpsilonNeck
