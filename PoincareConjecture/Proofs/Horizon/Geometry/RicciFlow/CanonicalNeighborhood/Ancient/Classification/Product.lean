import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.SimplyConnected
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.Noncollapse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

open RiemannianMetric

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_ancient_product_of_fixed_parallel_coordinate
    (K : AncientKappaSolution 3 M) {r : M → ℝ}
    (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hp : ∀ t ≤ 0, (K.flow.connection t).gradient r = (K.flow.connection 0).gradient r)
    (hu : ∀ t ≤ 0, HasUnitGradient (K.flow.connection t) r)
    (hz : ∀ t ≤ 0, HasZeroHessian (K.flow.connection t) r) :
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (_ : SecondCountableTopology N)
      (A : AncientKappaSolution 2 N), A.kappa = K.kappa / 2 ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
        (∀ z, r (e z) = z.2) ∧
        (∀ t ≤ 0, ∀ (z : N × ℝ) (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (K.flow.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
              (A.flow.metric t).inner z.1 a.1 b.1 + a.2 * b.2) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun q (_ : q ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient (hu 0 le_rfl) q
  let := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
  let H := K.flow.parallelGradientFactor hr (show (0 : ℝ) ∈ Iic 0 by simp) hu hz
  have hs (t : ℝ) (ht : t ≤ 0) :=
    exists_parallelGradient_productIsometry_curvature (n := 2)
      (K.complete t ht) hr (hu t ht) (hz t ht)
  let : ConnectedSpace (zeroLevelSet r) := (hs 0 le_rfl).2.1
  let : SecondCountableTopology (zeroLevelSet r) := (H.metric 0).secondCountableTopology
  have hn (t : ℝ) (ht : t ≤ 0) (y : zeroLevelSet r) :
      (H.connection t).curvatureTensorNorm y =
        (K.flow.connection t).curvatureTensorNorm (zeroLevelIncl r y) :=
    (parallelGradient_factor_curvature hr (hu t ht) (hz t ht) y).2.2.2.2.1
  let A : AncientKappaSolution 2 (zeroLevelSet r) :=
    { flow := H
      kappa := K.kappa / 2
      kappa_pos := div_pos K.kappa_pos (by norm_num)
      complete := fun t ht => (hs t ht).2.2.1
      nonnegative_curvature_operator := fun t ht y =>
        (parallelGradient_factor_curvature hr (hu t ht) (hz t ht) y).2.2.2.2.2
          (K.nonnegative_curvature_operator t ht _)
      bounded_curvature := by
        intro t ht
        obtain ⟨B, hB, hbound⟩ := K.bounded_curvature t ht
        exact ⟨B, hB, fun y => by rw [hn t ht]; exact hbound _⟩
      nonflat := by
        intro t ht
        obtain ⟨x, hx⟩ := K.nonflat t ht
        obtain ⟨_, _, _, _, d, _, _, _, _, _, _, hnorm, _⟩ := hs t ht
        exact ⟨(d.symm x).1, fun hzero => hx ((hnorm x).symm.trans hzero)⟩
      noncollapsed := K.flow.parallelGradientFactor_parabolic_noncollapsed
        K.complete hr hu hz hp K.noncollapsed }
  obtain ⟨_, _, _, Φ, e, h0, hΦ, he, hcoord, _, _, _, _⟩ := hs 0 le_rfl
  refine ⟨zeroLevelSet r, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    A, rfl, e, hcoord, ?_⟩
  intro t ht z a b
  obtain ⟨_, _, _, Ψ, d, hΨ0, hΨ, hd, _, hmetric, _⟩ := hs t ht
  have hde : d = e := by
    apply Diffeomorph.ext
    intro y
    rw [hd, he]
    have hcurve := hΨ (zeroLevelIncl r y.1)
    rw [hp t ht] at hcurve
    have hsame := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      ((K.flow.connection 0).contMDiff_gradient hr |>.of_le (by simp)) hcurve
      (hΦ (zeroLevelIncl r y.1))
      (show Ψ 0 (zeroLevelIncl r y.1) = Φ 0 (zeroLevelIncl r y.1) by rw [hΨ0, h0])
    exact congrFun hsame y.2
  rw [hde] at hmetric
  exact hmetric z a b

theorem exists_compact_round_product_of_terminal_null [SimplyConnectedSpace M]
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (_ : SecondCountableTopology N)
      (A : AncientKappaSolution 2 N),
      Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
        ∀ t ≤ 0, ∀ (z : N × ℝ) (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (K.flow.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
              (A.flow.metric t).inner z.1 a.1 b.1 + a.2 * b.2 := by
  obtain ⟨r, hr, _, hp⟩ :=
    K.exists_fixed_parallel_coordinate_of_simplyConnected x v w hv hw hvw hzero
  obtain ⟨N, hN, hT, hconn, hm, hb, hchart, hman, hsecond, A, _, e, _, he⟩ :=
    K.exists_ancient_product_of_fixed_parallel_coordinate hr
      (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2.1) (fun t ht => (hp t ht).2.2)
  exact ⟨N, hN, hT, hconn, hm, hb, hchart, hman, hsecond, A,
    P.two_dimensional_classification N A, e, he⟩

end PoincareConjecture.AncientKappaSolution
