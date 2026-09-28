import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Lift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Deck
import Mathlib.Analysis.Convex.Contractible










set_option autoImplicit false

open Set Function Topology
open scoped Manifold ContDiff

universe u

namespace Poincare.Topology


theorem semilocallySimplyConnectedSpace_of_chartedSpace (n : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    SemilocallySimplyConnectedSpace M := by
  apply SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected
  intro x
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ e.source := mem_chart_source _ _
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let U := e.symm '' Metric.ball (e x) r
  have hUopen : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hball
  have hxU : x ∈ U := ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩
  let : ContractibleSpace (Metric.ball (e x) r) :=
    (convex_ball (e x) r).contractibleSpace ⟨e x, Metric.mem_ball_self hr⟩
  let : ContractibleSpace U :=
    (e.symm.homeomorphOfImageSubsetSource hball rfl).contractibleSpace_iff.mp inferInstance
  exact ⟨U, hUopen.mem_nhds hxU, show SimplyConnectedSpace U from inferInstance⟩


theorem t2Space_of_isCoveringMap {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] {p : E → X} (hp : IsCoveringMap p) :
    T2Space E := by
  constructor
  intro e₁ e₂ hne
  by_cases he : p e₁ = p e₂
  · exact hp.isSeparatedMap e₁ e₂ he hne
  · obtain ⟨U, V, hU, hV, heU, heV, hUV⟩ := t2_separation he
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
      heU, heV, hUV.preimage p⟩

namespace UniversalCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [PathConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M]


@[instance_reducible] noncomputable def chartedSpace (x₀ : M) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (UniversalCover x₀) :=
  Poincare.Manifold.LocalHomeomorphLift.chartedSpace (isCoveringMap x₀).isLocalHomeomorph


theorem isManifold [IsManifold (𝓡 3) ∞ M] (x₀ : M) :
    letI := chartedSpace x₀
    IsManifold (𝓡 3) ∞ (UniversalCover x₀) :=
  Poincare.Manifold.LocalHomeomorphLift.isManifold
    (isCoveringMap x₀).isLocalHomeomorph (𝓡 3) ∞


theorem isLocalDiffeomorph [IsManifold (𝓡 3) ∞ M] (x₀ : M) :
    letI := chartedSpace x₀
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (proj (x₀ := x₀)) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph
    (isCoveringMap x₀).isLocalHomeomorph (𝓡 3) ∞

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in

theorem t2Space [T2Space M] (x₀ : M) : T2Space (UniversalCover x₀) :=
  t2Space_of_isCoveringMap (isCoveringMap x₀)



theorem t3Space [T2Space M] (x₀ : M) : T3Space (UniversalCover x₀) := by
  let := chartedSpace x₀
  let := t2Space x₀
  let : LocallyCompactSpace (UniversalCover x₀) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) (UniversalCover x₀)
  infer_instance

end UniversalCover

end Poincare.Topology

namespace PoincareConjecture.NeckOnlyCover

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem pathConnectedSpace_of_whole (H : NeckOnlyCover g) (hwhole : H.X = univ) :
    PathConnectedSpace M := by
  let : ConnectedSpace M := connectedSpace_iff_univ.mpr (hwhole ▸ H.connected_X)
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  exact PathConnectedSpace.of_locallyPathConnectedSpace

open Poincare.Topology

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_nonidentity_universalCover_transformation
    (H : NeckOnlyCover g) (hwhole : H.X = univ)
    (hns : ∀ N ∈ H.necks, N.IsNonseparating) (x₀ : M) :
    ∃ d : UniversalCover x₀ ≃ₜ UniversalCover x₀,
      UniversalCover.proj ∘ d = UniversalCover.proj ∧
        d ≠ Homeomorph.refl (UniversalCover x₀) := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := H.pathConnectedSpace_of_whole hwhole
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  exact exists_nonidentity_covering_transformation
    (UniversalCover.isCoveringMap x₀) (UniversalCover.surjective_proj x₀)
    (H.not_simplyConnectedSpace hns)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in



theorem exists_separating_universalCover_with_sheets (H : NeckOnlyCover g)
    (hwhole : H.X = univ)
    (x₀ : M) :
    letI : LocallyPathConnectedSpace M :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
    letI : PathConnectedSpace M := H.pathConnectedSpace_of_whole hwhole
    letI : SemilocallySimplyConnectedSpace M :=
      semilocallySimplyConnectedSpace_of_chartedSpace 3 M
    letI := UniversalCover.chartedSpace x₀
    letI := UniversalCover.isManifold x₀
    let p := UniversalCover.proj (x₀ := x₀)
    let hp := UniversalCover.isLocalDiffeomorph x₀
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        (∀ L ∈ H'.necks, L.IsSeparating) ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks,
          p '' L.central_sphere = N.central_sphere ∧
            p '' L.carrier = N.carrier ∧ InjOn p L.carrier := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := H.pathConnectedSpace_of_whole hwhole
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  let := UniversalCover.chartedSpace x₀
  let := UniversalCover.isManifold x₀
  let := UniversalCover.t2Space x₀
  let := UniversalCover.t3Space x₀
  let : MeasurableSpace (UniversalCover x₀) := borel (UniversalCover x₀)
  let : BorelSpace (UniversalCover x₀) := ⟨rfl⟩
  exact H.exists_separating_lifted_cover_with_sheets hwhole (UniversalCover.isCoveringMap x₀)
    (UniversalCover.isLocalDiffeomorph x₀)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_separating_universalCover (H : NeckOnlyCover g) (hwhole : H.X = univ)
    (x₀ : M) :
    letI : LocallyPathConnectedSpace M :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
    letI : PathConnectedSpace M := H.pathConnectedSpace_of_whole hwhole
    letI : SemilocallySimplyConnectedSpace M :=
      semilocallySimplyConnectedSpace_of_chartedSpace 3 M
    letI := UniversalCover.chartedSpace x₀
    letI := UniversalCover.isManifold x₀
    let p := UniversalCover.proj (x₀ := x₀)
    let hp := UniversalCover.isLocalDiffeomorph x₀
    ∃ H' : NeckOnlyCover (g.pullbackOfLocalDiffeomorph p hp),
      H'.X = univ ∧ H'.epsilon = H.epsilon ∧
        (∀ L ∈ H'.necks, L.IsSeparating) ∧
        ∀ L ∈ H'.necks, ∃ N ∈ H.necks, p '' L.central_sphere = N.central_sphere := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := H.pathConnectedSpace_of_whole hwhole
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  let := UniversalCover.chartedSpace x₀
  let := UniversalCover.isManifold x₀
  obtain ⟨H', hX, hε, hsep, hsheet⟩ :=
    H.exists_separating_universalCover_with_sheets hwhole x₀
  refine ⟨H', hX, hε, hsep, fun L hL => ?_⟩
  obtain ⟨N, hN, hs, _⟩ := hsheet L hL
  exact ⟨N, hN, hs⟩

end PoincareConjecture.NeckOnlyCover
