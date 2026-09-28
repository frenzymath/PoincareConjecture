import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SurfaceScalarConcentration
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.MaximalRank
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.ScalarRankGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

open Set Filter MeasureTheory
open PoincareConjecture Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

theorem PoincareConjecture.exists_uniform_unitBall_scalar_integral_bound_three :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        (g : PoincareConjecture.RiemannianMetric 3 M) (D : PoincareConjecture.LeviCivitaData g),
        PoincareConjecture.MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 3) x),
          -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M,
          (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  classical
  let δ : ℝ := 1/512
  let θ : ℝ := 1/8192
  let cminus := 1-δ^2/16
  let c := 1-δ^2/32
  let cplus := 1-δ^2/64
  have hδ : 0<δ := by norm_num [δ]
  have hδsmall : δ≤1/256 := by norm_num [δ]
  have hθ : 0<θ := by norm_num [θ]
  have hθpi : θ<Real.pi/2 := by
    dsimp [θ]
    linarith [Real.pi_gt_three]
  have hnear : 1-δ^2/8<cminus := by norm_num [cminus,δ]
  have hminus : cminus<c := by norm_num [cminus,c,δ]
  have hplus : c<cplus := by norm_num [c,cplus,δ]
  have hplus1 : cplus<1 := by norm_num [cplus,δ]
  have hc : 0≤c := by norm_num [c,δ]
  have hcθ : c<Real.cos (2*θ) := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := 2*θ)
    norm_num [c,δ,θ] at hcos ⊢
    linarith
  obtain ⟨_, hmaximal⟩ := exists_maximal_rank_scalar_counterexample_limit 3
    (by norm_num) θ hθ
  by_contra hfail
  obtain ⟨A, S, hproper, hgeo, hconv, hdiv, _, _, _, _, hmax⟩ := hmaximal hfail
  let : ProperSpace S.completedLimit.carrier := hproper
  have hlarge : ∀ K : ℝ, ∃ j, K < (A j).unitBallScalarIntegral := by
    intro K
    obtain ⟨j,hj⟩ := ((tendsto_atTop.1 hdiv) (K+1)).exists
    exact ⟨j,by linarith⟩
  obtain ⟨B,y,b,ρ,φ,ref,q,hB,hBasc,hBmax,hy,hspire,hb,hbcap,hρ,hρb,
      hascent,hφ,href,hconvref,hq,hpos,hazero,haqzero,hqzero,hmass⟩ :=
    RiemannianMetric.exists_surface_scalar_concentration_at_quarter_spire
      (fun j => (A j).metric) (fun j => (A j).connection)
      (fun j => (A j).complete) (fun j => (A j).sectional_lower)
      (fun j => (A j).point) hconv hgeo
      hδ hδsmall hnear hminus hplus hplus1
      (by norm_num : (0:ℝ)<1) le_rfl (by norm_num : (1:ℝ)<2) hlarge
  let : ProperSpace (S.completedLimit.rebase y).carrier := by
    change ProperSpace S.completedLimit.carrier
    exact hproper
  obtain ⟨_, hgrowth⟩ :=
    RiemannianMetric.exists_rescaled_pointed_limit_with_scalar_divergence_and_rank_growth_at_scaled_spire
      3 (by norm_num) θ hθ hθpi
  obtain ⟨ψ,hpos',rest⟩ := hgrowth
    (fun j => (A (φ j)).metric) (fun j => (A (φ j)).connection)
    (fun j => (A (φ j)).complete) (fun j => (A (φ j)).sectional_lower)
    ref q hconvref (σ := 1/4) (by norm_num) hc hcθ hminus hplus
    hρ (by linarith) hbcap hascent B hBmax
    (fun z hz => by
      change (1/4:ℝ)*B z ≤ dist z y
      simpa only [div_eq_mul_inv,mul_comm,one_mul] using hspire z hz)
    (fun j => (hq j).1) (fun j => (hq j).2.1) (fun j => (hq j).2.2) hmass
  let a : ℕ → ℝ := fun j => letI := (A (φ j)).metric.toMetricSpace
    badAscentRadius c b (q j)
  let G := fun j => rescaledMetric (A (φ (ψ j))).metric ((4*a (ψ j))^2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos' j))))
  let DS := fun j => rescaledMetric_connection (A (φ (ψ j))).metric
    (A (φ (ψ j))).connection ((4*a (ψ j))^2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos' j))))
  obtain ⟨S',hψ,hsmall,hproper',hgeo',hconv',_,_,_,_,hrank,hdiv'⟩ := rest
  have hsec' (j : ℕ) (x : (A (φ (ψ j))).carrier)
      (v w : TangentSpace (𝓡 3) x) : -1 ≤ (DS j).sectionalCurvature x v w := by
    have hh := rescaledMetric_sectionalCurvature_lower_bound (A (φ (ψ j))).metric
      (A (φ (ψ j))).connection ((4*a (ψ j))^2)⁻¹
      (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos' j)))) 1
      (A (φ (ψ j))).sectional_lower x v w
    simp only [one_div,inv_inv] at hh
    have hrpos : 0<4*a (ψ j) := mul_pos (by norm_num) (hpos' j)
    have hrle : 4*a (ψ j)≤1 := hsmall j
    change -1 ≤ (rescaledMetric_connection _ _ _ _).sectionalCurvature x v w
    nlinarith
  let A' : ℕ → PointedScalarModel 3 := fun j =>
    { carrier := (A (φ (ψ j))).carrier
      metric := G j
      connection := DS j
      point := q (ψ j)
      complete := metricComplete_rescaledMetric (A (φ (ψ j))).metric _ _
        (A (φ (ψ j))).complete
      sectional_lower := hsec' j }
  have hupper := hmax A' S' hproper' hgeo' hconv' hdiv'
  exact (not_lt_of_ge hupper) hrank
