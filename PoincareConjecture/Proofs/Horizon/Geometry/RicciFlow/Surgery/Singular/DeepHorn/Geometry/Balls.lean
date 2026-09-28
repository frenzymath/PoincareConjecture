import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.ScalarDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

theorem ball_subset_of_boundary_distance (horn : StrongHorn E epsilon)
    {x : (E.extended.slice T).carrier} (hx : x ∈ horn.carrier)
    {r : ℝ} (hboundary : ∀ y ∈ horn.boundary_sphere,
      ENNReal.ofReal r ≤ (E.extended.metric T).edist x y) :
    (E.extended.metric T).ball x r ⊆ horn.carrier := by
  intro y hy
  obtain ⟨gamma, hzero, hone, hgamma, _, hball⟩ :=
    (E.extended.metric T).exists_short_path_in_ball x y hy
  have hpre := isPreconnected_Icc.image gamma hgamma.continuousOn
  have hmeet : (gamma '' Icc (0 : ℝ) 1 ∩ horn.carrier).Nonempty :=
    ⟨x, ⟨0, ⟨le_rfl, zero_le_one⟩, hzero⟩, hx⟩
  have havoid : Disjoint (gamma '' Icc (0 : ℝ) 1) horn.boundary_sphere := by
    apply disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ hz
    exact not_lt_of_ge (hboundary _ hz) (hball ht)
  exact horn.subset_carrier_of_isPreconnected hpre hmeet havoid
    ⟨1, ⟨zero_le_one, le_rfl⟩, hone⟩

end StrongHorn

namespace DeepHorn

theorem exists_terminal_horn_ball_radius {K B : ℝ} (hK : 0 < K) (hB : 0 < B) :
    ∃ d : ℝ, 0 < d ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ (hM04 : RicciFlowCurvatureCalculus.{u}) (H : SingularTimeAssumptions F T M)
          (E : GeneralizedFlowExtension F T),
          H.r₀⁻¹ ^ 2 < K → H.analytic_constant = B →
          ∀ {epsilon : ℝ} (horn : StrongHorn E epsilon),
            (∀ y ∈ horn.boundary_sphere, (E.extended.connection T).scalarCurvature y ≤ K) →
            ∀ x ∈ horn.carrier, 2 * K ≤ (E.extended.connection T).scalarCurvature x →
              (E.extended.metric T).ball x d ⊆ horn.carrier := by
  obtain ⟨d, hd, hdist⟩ := exists_scalar_level_distance.{u} hK hB
  refine ⟨d, hd, ?_⟩
  intro F T M _ _ _ _ _ _ _ _ hM04 H E hcutoff hconstant epsilon horn hboundary x hx hhigh
  apply horn.ball_subset_of_boundary_distance hx
  intro y hy
  apply hdist (E.extended.connection T) ?_ x y hhigh (hboundary y hy)
  intro z hz v hv
  simpa only [hconstant] using terminal_scalar_gradient_bound hM04 H E z
    (hcutoff.trans_le hz) v hv

end DeepHorn
end PoincareConjecture
