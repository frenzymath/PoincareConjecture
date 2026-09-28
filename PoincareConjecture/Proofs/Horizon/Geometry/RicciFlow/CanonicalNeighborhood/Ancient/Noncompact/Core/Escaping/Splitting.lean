import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Line
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.CarrierLift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.AncientFactor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

open RiemannianMetric

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

theorem AncientKappaSolution.exists_round_factor_of_line_of_services
    (P : NoncompactKappaServices.{u})
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (K : AncientKappaSolution 3 M) (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, (K.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = K.kappa / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (K.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (K.flow.connection t).curvatureTensorNorm x) := by
  obtain ⟨B, hB, hbound⟩ := K.bounded_curvature 0 le_rfl
  have hancient (t : ℝ) (ht : t ≤ 0) (x : M) :
      (K.flow.connection t).curvatureTensorNorm x ≤ (3 : ℝ) ^ 2 * B :=
    (P.past_norm_le_scalar M K t 0 ht le_rfl x).trans
      ((le_abs_self _).trans
        (((K.flow.connection 0).abs_scalarCurvature_le_curvatureTensorNorm x).trans
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound x)) (sq_nonneg _))))
  obtain ⟨N⟩ := P.normalization M K (γ 0) 0 le_rfl
  have hscalar : 0 < (K.flow.connection 0).scalarCurvature (γ 0) :=
    N.scale_eq ▸ N.scale_pos
  let f := (K.flow.metric 0).busemann γ
  obtain ⟨hf, hu, _, hconn, A, _, hconstant, e, _, hmetric, hnorm⟩ :=
    K.flow.exists_ancientKappaSolution_factor_of_minimizing_line
      ricciFlowCurvatureTheory K.complete K.nonnegative_curvature_operator
      (mul_nonneg (sq_nonneg _) hB) hancient K.kappa_pos K.noncollapsed
      ⟨γ 0, hscalar⟩ γ hγ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let C := FlowCarrier.ofConnectedManifold 2 (zeroLevelSet f)
  exact ⟨C, A, hconstant, P.two_dimensional_classification (zeroLevelSet f) A,
    e, hmetric, hnorm⟩

theorem AncientKappaSolution.exists_round_factor_of_line_m26
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (K : AncientKappaSolution 3 M) (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, (K.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = K.kappa / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (K.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (K.flow.connection t).curvatureTensorNorm x) := by
  exact AncientKappaSolution.exists_round_factor_of_line_of_services P.noncompactServices K γ hγ

attribute [local instance] RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

theorem M23TerminalExtension.exists_round_factor_of_line_of_services
    (P : NoncompactKappaServices.{u})
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (_hterminal : M23TerminalExtension G)
    (γ : ℝ → G.limit.carrier.carrier)
    (hγ : ∀ s t : ℝ, (G.limit.flow.flow.metric 0).edist (γ s) (γ t) =
      ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = G.limit.flow.kappa / 2 ∧
        Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
            G.limit.carrier.carrier,
          ∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (G.limit.flow.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2 := by
  let K : AncientKappaSolution 3 (ULift.{u} G.limit.carrier.carrier) := G.limit.flow.ulift
  have hline (s t : ℝ) :
      (K.flow.metric 0).edist (ULift.up (γ s)) (ULift.up (γ t)) =
        ENNReal.ofReal |s - t| := by
    simpa only [K, AncientKappaSolution.ulift_edist] using hγ s t
  obtain ⟨C, A, hconstant, hround, e, hmetric, _⟩ :=
    K.exists_round_factor_of_line_of_services P (fun s => ULift.up (γ s)) hline
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) G.limit.carrier.carrier
  refine ⟨C, A, hconstant, hround, e.trans d, ?_⟩
  intro t ht z v w
  have hd := d.mdifferentiable (by simp) (e z)
  have he := e.mdifferentiable (by simp) z
  change (G.limit.flow.flow.metric t).inner (d (e z))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (d ∘ e) z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (d ∘ e) z w) = _
  rw [mfderiv_comp z hd he]
  exact hmetric t ht z v w

theorem M23TerminalExtension.exists_round_factor_of_line
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (_hterminal : M23TerminalExtension G)
    (γ : ℝ → G.limit.carrier.carrier)
    (hγ : ∀ s t : ℝ, (G.limit.flow.flow.metric 0).edist (γ s) (γ t) =
      ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = G.limit.flow.kappa / 2 ∧
        Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
            G.limit.carrier.carrier,
          ∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (G.limit.flow.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2 := by
  exact M23TerminalExtension.exists_round_factor_of_line_of_services P.noncompactServices _hterminal γ hγ

end PoincareConjecture
