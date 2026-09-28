import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ParameterRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.TerminalBallTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.ParametrizedTerminalJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Parametrized.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

theorem exists_terminal_cylinder_parametrized_jet_constant
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (hJ : IsCompact J) (d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {a b : ℝ} {S : PointedFlowSequence 3 a b}
        (G : PointedGeometricConvergence S), a < 0 ∧ 0 < b →
        G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) →
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
        (C : ℕ → FlowCarrier.{u} 3) (I : ℕ → Set ℝ)
        (F : ∀ k, RicciFlow 3 (C k).carrier (I k))
        (Ψ : ∀ k, (S.carrier k).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (C k).carrier)
        (A radius : ℕ → ℝ),
        Tendsto A atTop atTop → Tendsto radius atTop atTop →
        (∀ k, IsOpen (I k)) →
        (∀ k, Icc (-A k) 0 ⊆ interior (I k)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
          ((F k).connection t).NonnegativeCurvatureOperator x) →
        (∀ k, ∀ t ∈ Icc (-A k) 0,
          ∀ x ∈ ((F k).metric 0).ball (Ψ k (S.flow k).base) (radius k),
            ((F k).connection t).scalarCurvature x ≤ 4) →
      ∀ {δ s : ℝ}, 0 < δ → δ ≤ 1 → (1 / 2 : ℝ) ≤ s → s ≤ 1 →
        (∀ k, ∀ (x : (S.carrier k).carrier) (v w : TangentSpace (𝓡 3) x),
          ((S.flow k).metricAt 0).inner x v w =
            ((F k).metric (-δ)).inner (Ψ k x)
              (mfderiv (𝓡 3) (𝓡 3) (Ψ k) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Ψ k) x w)) →
        (fun z v w => s * roundCylinderPullback (G.limitFlow.metricAt 0) Φ z v w) =
          EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∀ q : UnitTwoSphere, ∀ r ∈ J, ∀ j ≤ d,
          let e : RoundCylinderCoordinates → (C (G.subsequence i)).carrier :=
            fun y => Ψ (G.subsequence i) (((G.embedding i).toFun
              (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2)
          ‖iteratedFDeriv ℝ j (((F (G.subsequence i)).metric 0).parametrizedCoefficients e)
              (0, r) -
            iteratedFDeriv ℝ j (((F (G.subsequence i)).metric (-δ)).parametrizedCoefficients e)
              (0, r)‖ ≤ B * δ := by
  classical
  let K : Set RoundCylinderCoordinates := {0} ×ˢ J
  have hK : IsCompact K := isCompact_singleton.prod hJ
  have hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ := by
    rintro x ⟨hx, _⟩
    exact ⟨by simpa only [mem_singleton_iff.mp hx] using
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)), mem_univ _⟩
  obtain ⟨Z, hZ, hinit⟩ := exists_eventual_cylinder_parametrized_jet_bounds
    hK hKU (by norm_num : (0 : ℝ) < 1 / 2)
  let L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨B, hB, htime⟩ :=
    RicciFlow.eventually_terminal_parametrizedJet_control_of_expanding_cylinders
      hC (m := 2) (by norm_num) L d Z (a := 1 / 2) (b := 7)
      (by norm_num) (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro a b S G hzero hcomplete Φ C I F Ψ A radius hA hradius hopen hI
    hcompleteF hoperator hscalar δ s hδ hδone hs hsone hmetric hround
  have htimes : ∀ᶠ k in atTop, Icc (-δ) 0 ⊆ interior (I k) := by
    filter_upwards [hA.eventually_ge_atTop 1] with k hk
    exact (Icc_subset_Icc (by linarith) le_rfl).trans (hI k)
  have hRic : ∀ᶠ k in atTop, ∀ t ∈ Icc (-δ) 0, ∀ x : (C k).carrier,
      ∀ v : TangentSpace (𝓡 3) x, 0 ≤ ((F k).connection t).ricci x v v := by
    filter_upwards [hA.eventually_ge_atTop 1] with k hk t ht x v
    exact (((F k).connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus 3 (C k).carrier ((F k).metric t) ((F k).connection t))
      x (hoperator k t ⟨by linarith [ht.1], ht.2⟩ x) v).1
  have hcompact : IsCompact (Φ '' (univ ×ˢ J)) :=
    (isCompact_univ.prod hJ).image Φ.continuous
  obtain ⟨R, hR, hdist⟩ :=
    G.exists_pos_eventually_embedding_edist_le_of_isometric_diffeomorph
      hzero hcomplete hcompact C F Ψ (by linarith : -δ ≤ 0)
      (Eventually.of_forall hmetric) htimes hRic
  have hterminal := htime C I F (fun k => Ψ k (S.flow k).base) A radius hA hradius
    hopen hI hcompleteF hoperator hscalar R hR.le
  have hinitial := hinit G hzero Φ.contMDiff hzero hs hround d
  have helliptic := G.eventually_cylinder_parametrized_center_ellipticity
    hzero Φ.contMDiff hzero (rmin := 1 / 2) (rmax := 1)
    (by norm_num) hs hsone hround hJ
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hterminal,
    hinitial, helliptic, G.eventually_cylinder_parametrizations_regular hzero Φ hK,
    hdist] with i ht hi hell hreg hd q r hr j hj
  obtain ⟨U, hU, hKU', hmap, hinvert⟩ := hreg q
  let e₀ : RoundCylinderCoordinates → (S.carrier (G.subsequence i)).carrier :=
    fun y => ((G.embedding i).toFun
      (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2
  let e := Ψ (G.subsequence i) ∘ e₀
  have hx : (0, r) ∈ U := hKU' ⟨rfl, hr⟩
  have hcoeff : ((S.flow (G.subsequence i)).metricAt 0).parametrizedCoefficients e₀ =
      ((F (G.subsequence i)).metric (-δ)).parametrizedCoefficients e :=
    RiemannianMetric.parametrizedCoefficients_diffeomorph _ _ (Ψ (G.subsequence i))
      (hmetric (G.subsequence i)) e₀
  have he : ContMDiffOn 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ e U := by
    intro x hx
    exact ((Ψ (G.subsequence i)).contMDiff.contMDiffAt.comp x
      (hmap.contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt
  have hei : ∀ x ∈ U,
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) e x).IsInvertible := by
    intro x hx
    change (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
      (Ψ (G.subsequence i) ∘ e₀) x).IsInvertible
    rw [mfderiv_comp x ((Ψ (G.subsequence i)).mdifferentiable (by simp) (e₀ x))
      ((hmap.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact (show (mfderiv (𝓡 3) (𝓡 3) (Ψ (G.subsequence i)) (e₀ x)).IsInvertible from
      ⟨(Ψ (G.subsequence i)).mfderivToContinuousLinearEquiv (by simp) (e₀ x), rfl⟩).comp
      (hinvert x hx)
  have hd' : ((F (G.subsequence i)).metric 0).edist
      (Ψ (G.subsequence i) (S.flow (G.subsequence i)).base) (e (0, r)) ≤
        ENNReal.ofReal R := by
    simpa only [e, e₀, Function.comp_apply,
      Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero] using
      hd (Φ (q, r)) (mem_image_of_mem Φ ⟨mem_univ _, hr⟩)
  apply ht hδ hδone hU he hei hx hd'
  · intro v
    rw [← hcoeff]
    have hv := hell q r hr v
    norm_num at hv
    exact hv
  · intro l hl
    rw [← hcoeff]
    exact hi l hl q (0, r) ⟨rfl, hr⟩
  · exact hj

end PoincareConjecture.PointedGeometricConvergence
