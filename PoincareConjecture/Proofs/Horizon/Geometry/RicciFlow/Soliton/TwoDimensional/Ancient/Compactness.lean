import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Compactness.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Exhaustion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactTimeConvergence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem compactSpace_of_compact_limit (G : AncientCompactTimeConvergence S)
    (hcompact :
      letI : TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
      CompactSpace G.limit.carrier.carrier) : CompactSpace M := by
  let : TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limit.carrier.carrier :=
    G.limit.carrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
  let : CompactSpace G.limit.carrier.carrier := hcompact
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset isCompact_univ
  have hmem (x : G.limit.carrier.carrier) : x ∈ G.exhaustion j := hj (mem_univ x)
  let f : G.limit.carrier.carrier → M := fun x => ((G.embedding j).toFun (-1, x)).2
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f := fun x =>
    (G.embedding j).spatialMap_contMDiffAt (G.exhaustion_open j)
      (G.time_window_base j) (hmem x)
  have hbij : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := fun x =>
    (G.embedding j).spatialMap_mfderiv_bijective (G.exhaustion_open j)
      (G.time_window_base j) (hmem x)
  have hopen : IsOpen (range f) :=
    (Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hf hbij).isOpenMap.isOpen_range
  have hc : IsCompact (range f) := by simpa using isCompact_univ.image hf.continuous
  have hu : range f = univ :=
    (show IsClopen (range f) from ⟨hc.isClosed, hopen⟩).eq_univ
      ⟨f G.limit.base, mem_range_self G.limit.base⟩
  exact ⟨hu ▸ hc⟩

end PoincareConjecture.AncientCompactTimeConvergence
