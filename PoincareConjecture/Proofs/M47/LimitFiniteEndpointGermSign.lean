import PoincareConjecture.Proofs.M47.LimitFiniteEndpointSourceSign
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointFlow
import PoincareConjecture.Proofs.M47.TerminalCurvatureSectionalLimit









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance endpointSignDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointSignDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance endpointSignBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointSignBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

private theorem operator_of_open_bilinear_jets
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (hJ : IsOpen J)
    (A : ℕ → RicciFlow 3 M J) (F : RicciFlow 3 M J)
    (hjet : ∀ (x : M) (r : ℕ) (K : Set (ℝ × E)), IsCompact K →
      K ⊆ J ×ˢ (extChartAt (𝓡 3) x).target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A k).metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2))
        (iteratedFDeriv ℝ r (fun p : ℝ × E =>
          (F.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2)) atTop K)
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ t ∈ J,
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((A k).connection t).sectionalCurvature x v w) :
    ∀ t ∈ J, ∀ x, (F.connection t).NonnegativeCurvatureOperator x := by
  have hscalar (x : M) (r : ℕ) (j b : Fin 3) (K : Set (ℝ × E))
      (hK : IsCompact K) (hKU : K ⊆ J ×ˢ (extChartAt (𝓡 3) x).target) :
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A k).metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2
            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
        (iteratedFDeriv ℝ r (fun p : ℝ × E =>
          (F.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2
            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
        atTop K := by
    let Ω := J ×ˢ (extChartAt (𝓡 3) x).target
    have hΩ : IsOpen Ω := hJ.prod (isOpen_extChartAt_target x)
    have hsmooth (G : RicciFlow 3 M J) :
        ContDiffOn ℝ ∞ (fun p : ℝ × E =>
          (G.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2) Ω := by
      intro p hp
      exact (G.smooth.contDiffAt_spacetime_pullbackCoefficients hJ
        ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hp.2).contMDiffAt
          (extChartAt_target_mem_nhds' hp.2)) hp.1).contDiffWithinAt
    let L : V →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ j))
    have h := Poincare.Analysis.Calculus.smooth_convergence_continuousLinearMap_comp
      L hΩ (hsmooth F) (fun p hp => ⟨Ω, hΩ, hp,
        Eventually.of_forall fun k => hsmooth (A k)⟩) (hjet x)
    exact h.2 r K hK hKU
  intro t ht x
  have hj := RiemannianMetric.spatial_and_time_jets_of_spacetime_jets
    (fun k => (A k).metric) F.metric (fun k => (A k).smooth) F.smooth hJ ht x
    (fun r _ a b => RiemannianMetric.tendsto_spacetime_jet_of_compact_uniform r
      (hscalar x r a b) ⟨ht, mem_extChartAt_target x⟩)
  apply terminalCurvature_operator_of_coordinate_jets
    (fun k => (A k).connection t) (F.connection t) x hj.1
  intro eta heta
  exact (hlower eta heta).mono fun k hk => hk t ht

private theorem operator_of_open_chart_jets
    {ι : Type*} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (hJ : IsOpen J) (A : ℕ → RicciFlow 3 M J)
    (i : ι) (e : Piece U i → M)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e)
    (F : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      RicciFlow 3 (Piece U i) J)
    (B : ℝ × E → V)
    (hcoeff : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      ∀ t ∈ J, ∀ (x : Piece U i) v w, (F.metric t).inner x v w = B (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × E =>
        ((A k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization U hU e) p.2))
      (iteratedFDeriv ℝ m B) atTop K)
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ t ∈ J,
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((A k).connection t).sectionalCurvature x v w) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ t ∈ J, ∀ x, (F.connection t).NonnegativeCurvatureOperator x := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let Achart := fun k => (A k).pullbackToCanonicalDomain (U i) (hU i) e he
  apply operator_of_open_bilinear_jets hJ Achart F
  · intro x m K hK hKU
    rw [ChartDistance.canonical_extChartAt_target U hU] at hKU
    have hseq (k : ℕ) : EqOn
        (fun p : ℝ × E => ((A k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization U hU e) p.2)
        (fun p : ℝ × E => ((Achart k).metric p.1).pullbackCoefficients
          (extChartAt (𝓡 3) x).symm p.2) (J ×ˢ U i) := by
      intro p hp
      exact (ChartDistance.canonical_pullbackMetric_coefficients U hU
        ((A k).metric p.1) e he x ⟨p.2, hp.2⟩).symm
    have hlim : EqOn B (fun p : ℝ × E => (F.metric p.1).pullbackCoefficients
        (extChartAt (𝓡 3) x).symm p.2) (J ×ˢ U i) := by
      intro p hp
      have hform : B p = (F.metric p.1).inner ⟨p.2, hp.2⟩ := by
        ext v w
        exact (hcoeff p.1 hp.1 ⟨p.2, hp.2⟩ v w).symm
      exact hform.trans (RiemannianMetric.pullbackCoefficients_canonicalChart
        (U i) (hU i) (F.metric p.1) x ⟨p.2, hp.2⟩).symm
    exact ((hjet m K hK hKU).congr (Eventually.of_forall fun k =>
      (Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
        (hJ.prod (hU i)) (hseq k) m).mono hKU)).congr_right
      ((Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
        (hJ.prod (hU i)) hlim m).mono hKU)
  · intro eta heta
    filter_upwards [hlower eta heta] with k hk t ht x v w
    rw [M36.sectionalCurvature_eq_of_local_isometry ((Achart k).connection t)
      ((A k).connection t) (f := e) isOpen_univ he.contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ x) v w]
    exact hk t ht _ _ _



theorem limitFinite_endpoint_chart_operator
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {T d R ρ : ℝ} (hd : 0 < d) (hc : -T + d / 4 ≤ 0)
    (hρ : 0 < ρ) (hρR : ρ < R)
    (A : ℕ → RicciFlow 3 M (Icc (-(T + d / 2)) 0))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (hsource : Φ.source = Metric.ball 0 R) (B : ℝ × E → V)
    (hjets : ∀ m K, IsCompact K →
      K ⊆ Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 ρ → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun p : ℝ × E =>
          ((A k).metric (p.1 + (-T + d / 4))).pullbackCoefficients Φ p.2))
        (iteratedFDeriv ℝ m B) atTop K)
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ t ∈ Icc (-(T + d / 2)) 0,
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((A k).connection t).sectionalCurvature x v w) :
    let W := fun _ : Unit => Metric.ball (0 : E) ρ
    let hW : ∀ i, IsOpen (W i) := fun _ => Metric.isOpen_ball
    letI : Nonempty (W ()) := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
    letI := (hW ()).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hW ()).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ F : RicciFlow 3 (Piece W ()) (Ioo (-T - d / 8) (-T + d / 4)),
      (∀ t ∈ Ioo (-T - d / 8) (-T + d / 4), ∀ (x : Piece W ()) v w,
        (F.metric t).inner x v w = B (t - (-T + d / 4), x) v w) →
      ∀ t ∈ Ioo (-T - d / 8) (-T + d / 4), ∀ x,
        (F.connection t).NonnegativeCurvatureOperator x := by
  classical
  let W := fun _ : Unit => Metric.ball (0 : E) ρ
  let hW : ∀ i, IsOpen (W i) := fun _ => Metric.isOpen_ball
  let : Nonempty (W ()) := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let : ∀ i, Nonempty (Piece W i) := fun _ => ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let := (hW ()).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hW ()).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  dsimp only
  intro F hcoeff
  let J := Ioo (-((3 * d / 4) / 2)) 0
  let c := -T + d / 4
  let e : Piece W () → M := fun x => Φ x
  have he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
    intro x
    have hx : (x : E) ∈ Φ.source := by
      rw [hsource]
      exact Metric.ball_subset_ball hρR.le x.property
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (W ()) (hW ()) ∞ x).comp
      (𝓡 3) M (Φ.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx)
  have hnear (z : E) (hz : z ∈ W ()) :
      ChartDistance.chartParametrization W hW e =ᶠ[𝓝 z] Φ := by
    filter_upwards [(hW ()).mem_nhds hz] with y hy
    exact ChartDistance.chartParametrization_apply W hW e ⟨y, hy⟩
  have hmap : (fun s : ℝ => s + c) '' J ⊆ Icc (-(T + d / 2)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    dsimp [J, c] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  have hne : J.Nontrivial := by
    exact ⟨-d / 4, ⟨by linarith, by linarith⟩, -d / 8,
      ⟨by linarith, by linarith⟩, by linarith⟩
  let A' : ℕ → RicciFlow 3 M J := fun k => (A k).translate c hmap ordConnected_Ioo hne
  have hfmap : (fun s : ℝ => s + c) '' J ⊆ Ioo (-T - d / 8) (-T + d / 4) := by
    rintro _ ⟨s, hs, rfl⟩
    dsimp [J, c] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  let F' := F.translate c hfmap ordConnected_Ioo hne
  have hcoeff' : ∀ s ∈ J, ∀ (x : Piece W ()) v w,
      (F'.metric s).inner x v w = B (s, x) v w := by
    intro s hs x v w
    change (F.metric (s + c)).inner x v w = B (s, x) v w
    simpa only [c, add_sub_cancel_right] using hcoeff (s + c) (hfmap ⟨s, hs, rfl⟩) x v w
  have hactual (k : ℕ) : EqOn
      (fun p : ℝ × E => ((A k).metric (p.1 + c)).pullbackCoefficients Φ p.2)
      (fun p : ℝ × E => ((A' k).metric p.1).pullbackCoefficients
        (ChartDistance.chartParametrization W hW e) p.2) (J ×ˢ W ()) := by
    intro p hp
    have hn := hnear p.2 hp.2
    change ((A k).metric (p.1 + c)).pullbackCoefficients Φ p.2 =
      ((A k).metric (p.1 + c)).pullbackCoefficients
        (ChartDistance.chartParametrization W hW e) p.2
    unfold RiemannianMetric.pullbackCoefficients
    rw [hn.self_of_nhds, hn.mfderiv_eq]
  have hjetActual : ∀ m K, IsCompact K → K ⊆ J ×ˢ W () → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × E =>
        ((A' k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization W hW e) p.2))
      (iteratedFDeriv ℝ m B) atTop K := by
    intro m K hK hKΩ
    exact (hjets m K hK hKΩ).congr (Eventually.of_forall fun k =>
      (Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
        (isOpen_Ioo.prod (hW ())) (hactual k) m).mono hKΩ)
  have hlower' : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ s ∈ J,
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((A' k).connection s).sectionalCurvature x v w := by
    intro eta heta
    filter_upwards [hlower eta heta] with k hk s hs x v w
    exact hk (s + c) (hmap ⟨s, hs, rfl⟩) x v w
  have hop := operator_of_open_chart_jets W hW isOpen_Ioo A' () e he F' B
    hcoeff' hjetActual hlower'
  intro t ht x
  have hs : t - c ∈ J := by
    dsimp [J, c]
    constructor <;> linarith [ht.1, ht.2]
  have h := hop (t - c) hs x
  change (F.connection (t - c + c)).NonnegativeCurvatureOperator x at h
  convert h using 1 <;> congr 1 <;> ring

end PoincareConjecture.M47
