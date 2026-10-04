import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Identification.AncientIdentification
import PoincareLib.Geometry.RicciFlow.Splitting.ParallelGradient.AncientFactor
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornTheory

/-!
# A compact round factor of the retained ancient limit

A specified minimizing line and a single uniform bound over all past times
give an ancient surface factor of the actual infinite-horizon M30 limit.
The supplied M19 service gives its compact positive-round certificate, and
one fixed product diffeomorphism retains every past metric and curvature norm.

The packaging rederives
`AncientKappaSolution.exists_compact_round_surface_product_of_minimizing_line`
from `AncientKappa/Compactness/Boundedness/Factor` at universe `u`, using
`RicciFlow.exists_ancientKappaSolution_factor_of_minimizing_line` and
`FlowCarrier.ofConnectedManifold` with the supplied M32 predecessor services.

Sources: Morgan--Tian, Corollary 9.50(3), printed pp. 213-214, and the
final ancient-limit argument after Claim 11.35, p. 291. See
`proof-work/tasks/M32/derivations/claim11_35-ancient-round-factor.md`.
-/

noncomputable section
set_option autoImplicit false

universe u

namespace PoincareMT.M32

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

/-- The supplied M04 and M19 services give a compact positive-round ancient
surface factor at the original universe, with one product map for all past
times. Morgan--Tian, Corollary 9.50(3), pp. 213-214, and the final argument
after Claim 11.35, p. 291. The uniform all-time bound and exact line are inputs. -/
theorem exists_compact_round_surface_product_of_minimizing_line
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (P : RepairedHornSelectionPredecessors.{u}) (F : RicciFlow 3 M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ B)
    {κ : ℝ} (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed F κ)
    (hscalar : ∃ p, 0 < (F.connection 0).scalarCurvature p)
    (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, (F.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = κ / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (F.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (F.connection t).curvatureTensorNorm x) := by
  let : SecondCountableTopology M := (F.metric 0).secondCountableTopology
  let f := (F.metric 0).busemann γ
  obtain ⟨hf, hu, _, hconn, A, _, hconstant, e, _, hmetric, hnorm⟩ :=
    F.exists_ancientKappaSolution_factor_of_minimizing_line
      P.m04 hc hop hB hbound hκ hnc hscalar γ hγ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := Poincare.Geometry.Manifold.RegularLevel.openLevelSetChartedSpace hf
    (⊤ : TopologicalSpace.Opens M)
    (fun x _ => RiemannianMetric.regular_of_hasUnitGradient hu x) 2 0
  let := Poincare.Geometry.Manifold.RegularLevel.isManifold_openLevelSet hf
    (⊤ : TopologicalSpace.Opens M)
    (fun x _ => RiemannianMetric.regular_of_hasUnitGradient hu x) 2 0
  let : ConnectedSpace (RiemannianMetric.zeroLevelSet f) := hconn
  let C := FlowCarrier.ofConnectedManifold 2 (RiemannianMetric.zeroLevelSet f)
  exact ⟨C, A, hconstant, P.m19_round A, e, hmetric, hnorm⟩

/-- The actual M30 ancient identification gives a compact positive-round
surface factor of the original normalized limit, retaining its metrics and
curvature norms at every past time. Morgan--Tian, the final argument after
Claim 11.35, p. 291, using Corollary 9.50(3), pp. 213-214. -/
theorem m30AncientIdentification_exists_compact_round_surface_product
    (P : RepairedHornSelectionPredecessors.{u})
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) {κ : ℝ}
    (I : M30AncientKappaIdentification L κ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ≤ 0, ∀ x, (L.flow.connection t).curvatureTensorNorm x ≤ B)
    (γ : ℝ → L.carrier.carrier)
    (hγ : ∀ s t : ℝ,
      (L.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = κ / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.carrier.carrier,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (L.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (L.flow.connection t).curvatureTensorNorm x) := by
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  let K := I.certificate.solution
  have hboundK : ∀ t ≤ 0, ∀ x, (K.flow.connection t).curvatureTensorNorm x ≤ B := by
    intro t ht x
    rw [m30AncientIdentification_curvatureTensorNorm_eq L I t ht x]
    exact hbound t ht x
  have hscalar : ∃ p, 0 < (K.flow.connection 0).scalarCurvature p := by
    refine ⟨L.base, ?_⟩
    rw [m30AncientIdentification_scalarCurvature_eq L I 0 le_rfl L.base,
      L.scalar_normalized]
    exact zero_lt_one
  have hγK : ∀ s t : ℝ,
      (K.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
    intro s t
    rw [I.certificate.metric_eq 0 le_rfl]
    exact hγ s t
  obtain ⟨C, hC⟩ := exists_compact_round_surface_product_of_minimizing_line
    P K.flow K.complete K.nonnegative_curvature_operator hB hboundK
    K.kappa_pos K.noncollapsed hscalar γ hγK
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  obtain ⟨A, hkappa, hround, e, hmetric, hnorm⟩ := hC
  refine ⟨C, A, hkappa.trans (congrArg (fun k : ℝ => k / 2) I.certificate.kappa_eq),
    hround, e, ?_, ?_⟩
  · intro t ht z v w
    rw [← I.certificate.metric_eq t ht]
    exact hmetric t ht z v w
  · intro t ht x
    exact (hnorm t ht x).trans (m30AncientIdentification_curvatureTensorNorm_eq L I t ht x)

/-- The infinite-horizon M30 conclusion's retained ancient field gives a
compact positive-round product for that same final limit. The exact line and
one all-time curvature bound remain explicit. Morgan--Tian, the final argument
after Claim 11.35, p. 291, using Corollary 9.50(3), pp. 213-214. -/
theorem longBlowupConclusion_exists_compact_round_surface_product
    (P : RepairedHornSelectionPredecessors.{u})
    {S : GeneralizedBlowupSequence.{u}} {κ r₀ : ℝ}
    (G : RepairedLongControlledBlowupConclusion S κ r₀ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ≤ 0, ∀ x,
      (G.convergence.limit.flow.connection t).curvatureTensorNorm x ≤ B)
    (γ : ℝ → G.convergence.limit.carrier.carrier)
    (hγ : ∀ s t : ℝ,
      (G.convergence.limit.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = κ / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
            G.convergence.limit.carrier.carrier,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (G.convergence.limit.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (G.convergence.limit.flow.connection t).curvatureTensorNorm x) := by
  obtain ⟨I⟩ := G.ancient rfl
  exact m30AncientIdentification_exists_compact_round_surface_product
    P G.convergence.limit I hB hbound γ hγ

end PoincareMT.M32
