import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TwoGeodesics
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TotalExponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Geodesic.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.FlatMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Transitions
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Euclidean
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.Gaussian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flat.Exponential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle BigOperators

namespace PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]

structure FlatShrinkingPotentialData where
  metric : RiemannianMetric n M
  connection : LeviCivitaData metric
  complete : MetricComplete metric
  potential : M → ℝ
  tau : ℝ
  tau_pos : 0 < tau
  potential_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ potential
  hessian_eq : ∀ x (u v : TangentSpace (𝓡 n) x),
    connection.hessian potential x u v = (1 / (2 * tau)) * metric.inner x u v
  gradient_eq : ∀ x,
    potential x = tau * metric.inner x (connection.gradient potential x)
      (connection.gradient potential x)
  flat : ∀ x, connection.curvatureTensorNorm x = 0

namespace FlatShrinkingPotentialData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem potential_nonneg (S : FlatShrinkingPotentialData (n := n) (M := M)) (x : M) :
    0 ≤ S.potential x := by
  rw [S.gradient_eq]
  exact mul_nonneg S.tau_pos.le (by
    by_cases hv : S.connection.gradient S.potential x = 0
    · simp [hv]
    · exact (S.metric.pos x _ hv).le)

private theorem tangentNorm_sq_eq_inner (S : FlatShrinkingPotentialData (n := n) (M := M))
    (x : M) (v : TangentSpace (𝓡 n) x) :
    S.metric.tangentNorm x v ^ 2 = S.metric.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  change Real.sqrt (S.metric.inner x v v) ^ 2 = _
  exact Real.sq_sqrt (by
    by_cases hv : v = 0
    · simp [hv]
    · exact (S.metric.pos x v hv).le)

private theorem globalGeodesic_inner_velocity_eq_initial
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    S.metric.inner (S.metric.globalGeodesic S.complete p v t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (S.metric.globalGeodesic S.complete p v) t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (S.metric.globalGeodesic S.complete p v) t 1) =
      S.metric.inner p v v := by
  let γ := S.metric.globalGeodesic S.complete p v
  have hgeo : S.metric.IsGeodesicOn γ univ :=
    (S.metric.globalGeodesic_spec S.complete p v).1
  have hspeed : ∀ t, S.metric.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) =
      S.metric.tangentNorm p v := by
    intro t
    have hconst := isOpen_univ.is_const_of_deriv_eq_zero
      (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      (fun s _ => (hgeo.hasDerivAt_tangentNorm_zero (mem_univ s)).differentiableAt
        |>.differentiableWithinAt)
      (fun s _ => (hgeo.hasDerivAt_tangentNorm_zero (mem_univ s)).deriv)
      (mem_univ t) (mem_univ 0)
    rw [hconst]
    have hv := S.metric.mfderiv_globalGeodesic_zero S.complete p v
    change S.metric.tangentNorm (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) = S.metric.tangentNorm p v
    rw [show γ = S.metric.globalGeodesic S.complete p v from rfl, hv]
    rw [(S.metric.globalGeodesic_spec S.complete p v).2.1]
  rw [← tangentNorm_sq_eq_inner S, ← tangentNorm_sq_eq_inner S, hspeed]

private theorem deriv_comp_globalGeodesic_at_zero
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) :
    deriv (S.potential ∘ S.metric.globalGeodesic S.complete p v) 0 =
      S.metric.inner p (S.connection.gradient S.potential p) v := by
  let γ := S.metric.globalGeodesic S.complete p v
  have hγall : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ :=
    PoincareConjecture.RiemannianMetric.contMDiff_global_geodesic
      (S.metric.globalGeodesic_spec S.complete p v).1
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ 0 := hγall 0
  have hcomp := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (I'' := 𝓘(ℝ, ℝ)) 0
      ((S.potential_smooth (γ 0)).mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at hcomp
  change deriv (S.potential ∘ γ) 0 =
    mvfderiv (𝓡 n) S.potential (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at hcomp
  have hvel := S.metric.mfderiv_globalGeodesic_zero S.complete p v
  have hp := (S.metric.globalGeodesic_spec S.complete p v).2.1
  dsimp only [γ] at hcomp
  have hvel' : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = v := by
    simpa only [γ] using hvel
  rw [hvel', hp] at hcomp
  simpa only [← S.connection.inner_gradient] using hcomp

theorem potential_globalGeodesic_eq_quadratic
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    S.potential (S.metric.globalGeodesic S.complete p v t) =
      S.potential p + t * S.metric.inner p
        (S.connection.gradient S.potential p) v +
        (t ^ 2 / 2) * (1 / (2 * S.tau)) * S.metric.inner p v v := by
  let γ := S.metric.globalGeodesic S.complete p v
  let φ := S.potential ∘ γ
  let a := (1 / (2 * S.tau)) * S.metric.inner p v v
  have hgeo : S.metric.IsGeodesicOn γ univ :=
    (S.metric.globalGeodesic_spec S.complete p v).1
  have hsecond (s : ℝ) : HasDerivAt (deriv φ) a s := by
    have h := S.connection.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn
      isOpen_univ S.potential_smooth.contMDiffOn hgeo (mem_univ s) (mem_univ _)
    rw [S.hessian_eq] at h
    convert h using 1
    dsimp [a]
    rw [show γ = S.metric.globalGeodesic S.complete p v from rfl]
    rw [S.globalGeodesic_inner_velocity_eq_initial p v s]
  have hq (s : ℝ) : deriv φ s = deriv φ 0 + a * s := by
    have hz (u : ℝ) : HasDerivAt (fun z : ℝ => deriv φ z - a * z) 0 u := by
      convert! (hsecond u).sub ((hasDerivAt_id u).const_mul a) using 1
      simp
    have hconst := isOpen_univ.is_const_of_deriv_eq_zero
      (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      (fun u _ => (hz u).differentiableAt.differentiableWithinAt)
      (fun u _ => (hz u).deriv) (mem_univ s) (mem_univ 0)
    have := congrArg (fun z : ℝ => z + a * s) hconst
    linarith
  have hφsmooth : ContDiff ℝ ∞ φ :=
    contMDiff_iff_contDiff.mp
      (S.potential_smooth.comp
        (PoincareConjecture.RiemannianMetric.contMDiff_global_geodesic hgeo))
  have hφdiff : Differentiable ℝ φ := hφsmooth.differentiable (by simp)
  have hfirst (s : ℝ) : HasDerivAt φ (deriv φ s) s := by
    exact (hφdiff s).hasDerivAt
  have hpoly (s : ℝ) : HasDerivAt
      (fun u : ℝ => φ 0 + deriv φ 0 * u + a * u ^ 2 / 2)
      (deriv φ 0 + a * s) s := by
    convert! (((hasDerivAt_const s (φ 0)).add
      ((hasDerivAt_id s).const_mul (deriv φ 0))).add
      (((hasDerivAt_id s).pow 2).const_mul a |>.div_const 2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have heq : φ t = φ 0 + deriv φ 0 * t + a * t ^ 2 / 2 := by
    exact isOpen_univ.eqOn_of_deriv_eq
      (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      hφdiff.differentiableOn
      (fun u _ => (hpoly u).differentiableAt.differentiableWithinAt)
      (fun u _ => (hq u).trans ((hpoly u).deriv.symm))
      (mem_univ 0) (by simp) (mem_univ t)
  have hφ0 : φ 0 = S.potential p := by
    simp [φ, γ, (S.metric.globalGeodesic_spec S.complete p v).2.1]
  rw [hφ0, S.deriv_comp_globalGeodesic_at_zero p v] at heq
  simpa [φ, a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using heq

theorem exists_potential_zero
    (S : FlatShrinkingPotentialData (n := n) (M := M)) :
    ∃ p : M, S.potential p = 0 ∧ S.connection.gradient S.potential p = 0 := by
  classical
  let q : M := Classical.choice inferInstance
  by_cases hq : S.connection.gradient S.potential q = 0
  · refine ⟨q, ?_, hq⟩
    rw [S.gradient_eq, hq]
    simp
  let v : EuclideanSpace ℝ (Fin n) := -(2 * S.tau) • S.connection.gradient S.potential q
  let p := S.metric.globalGeodesic S.complete q v 1
  have hformula := S.potential_globalGeodesic_eq_quadratic q v 1
  have hqgrad := S.gradient_eq q
  have hinner : S.metric.inner q (S.connection.gradient S.potential q)
      (S.connection.gradient S.potential q) = S.potential q / S.tau := by
    apply (eq_div_iff (ne_of_gt S.tau_pos)).2
    rw [hqgrad]
    ring
  have hzero : S.potential p = 0 := by
    change S.potential (S.metric.globalGeodesic S.complete q v 1) = 0
    rw [hformula]
    simp only [v]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hinner]
    field_simp [ne_of_gt S.tau_pos]
    ring
  have hgrad : S.connection.gradient S.potential p = 0 := by
    rw [S.gradient_eq] at hzero
    have hinner0 : S.metric.inner p (S.connection.gradient S.potential p)
        (S.connection.gradient S.potential p) = 0 := by
      nlinarith [hzero, S.tau_pos]
    by_contra hne
    exact (ne_of_gt (S.metric.pos p _ hne)) hinner0
  exact ⟨p, hzero, hgrad⟩

theorem globalGeodesic_terminal_velocity
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    (hp : S.potential p = 0) (hpgrad : S.connection.gradient S.potential p = 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (S.metric.globalGeodesic S.complete p v) 1 1 =
      (2 * S.tau) • S.connection.gradient S.potential
        (S.metric.globalGeodesic S.complete p v 1) := by
  let γ := S.metric.globalGeodesic S.complete p v
  let q := γ 1
  let u := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1
  let G := S.connection.gradient S.potential q
  let a := S.metric.inner p v v
  have hpoly : (S.potential ∘ γ) =
      fun t : ℝ => (t ^ 2 / 2) * (1 / (2 * S.tau)) * a := by
    funext t
    simpa [γ, hp, hpgrad, a] using S.potential_globalGeodesic_eq_quadratic p v t
  have hd : HasDerivAt (S.potential ∘ γ) (a / (2 * S.tau)) 1 := by
    rw [hpoly]
    convert! ((((hasDerivAt_id (1 : ℝ)).pow 2).div_const 2).mul_const
      (1 / (2 * S.tau))).mul_const a using 1 <;> norm_num <;> ring
  have hγ := (S.metric.globalGeodesic_spec S.complete p v).1
  have hc := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (I'' := 𝓘(ℝ, ℝ)) 1
      ((S.potential_smooth q).mdifferentiableAt (by simp))
      ((hγ.contMDiffAt (mem_univ 1)).mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at hc
  change deriv (S.potential ∘ γ) 1 = mvfderiv (𝓡 n) S.potential q u at hc
  rw [hd.deriv, ← S.connection.inner_gradient] at hc
  have hpair : (2 * S.tau) * S.metric.inner q G u = a := by
    have h := (div_eq_iff (mul_ne_zero (by norm_num) S.tau_pos.ne')).mp hc
    dsimp only [G]
    nlinarith [h]
  have hspeed : S.metric.inner q u u = a :=
    S.globalGeodesic_inner_velocity_eq_initial p v 1
  have hpot : 4 * S.tau * S.potential q = a := by
    have h := congrFun hpoly 1
    change S.potential q = _ at h
    norm_num at h
    rw [h]
    field_simp [ne_of_gt S.tau_pos]
    ring
  have hgrad : S.potential q = S.tau * S.metric.inner q G G := S.gradient_eq q
  rw [hgrad] at hpot
  have hnorm : S.metric.inner q (u - (2 * S.tau) • G)
      (u - (2 * S.tau) • G) = 0 := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [S.metric.symm q u G, hspeed]
    nlinarith [hpair, hpot]
  have hz : u - (2 * S.tau) • G = 0 := by
    by_contra hne
    exact (ne_of_gt (S.metric.pos q _ hne)) hnorm
  exact sub_eq_zero.mp hz

private theorem hasDerivAt_globalGeodesic_endpoint_chart
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    let γ := S.metric.globalGeodesic S.complete p v
    HasDerivAt (fun s => extChartAt (𝓡 n) (γ t) (γ s))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) t := by
  dsimp only
  let γ := S.metric.globalGeodesic S.complete p v
  have hγ := ((S.metric.globalGeodesic_spec S.complete p v).1.contMDiffAt
    (mem_univ t)).mdifferentiableAt (by simp)
  have hc := (contMDiffAt_extChartAt (I := 𝓡 n) (n := ∞) (x := γ t)).mdifferentiableAt
    (by simp)
  have hd := (hc.comp t hγ).differentiableAt.hasDerivAt
  have hchain := congrArg (fun A => A (1 : ℝ)) (mfderiv_comp t hc hγ)
  rw [mfderiv_eq_fderiv] at hchain
  simp only [mfderiv_extChartAt_self] at hchain
  exact hd.congr_deriv hchain

theorem globalExponential_injective
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    (hp : S.potential p = 0) (hpgrad : S.connection.gradient S.potential p = 0) :
    Function.Injective (S.metric.globalExponential S.complete p) := by
  intro v w hvw
  let γ := S.metric.globalGeodesic S.complete p v
  let η := S.metric.globalGeodesic S.complete p w
  have hγ := (S.metric.globalGeodesic_spec S.complete p v).1
  have hη := (S.metric.globalGeodesic_spec S.complete p w).1
  have hpos : γ 1 = η 1 := hvw
  have hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1 := by
    rw [S.globalGeodesic_terminal_velocity p hp hpgrad v,
      S.globalGeodesic_terminal_velocity p hp hpgrad w]
    rw [show S.metric.globalGeodesic S.complete p v 1 =
      S.metric.globalGeodesic S.complete p w 1 from hpos]
  have hchartγ : HasDerivAt (fun t => extChartAt (𝓡 n) (γ 1) (γ t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) 1 := by
    exact S.hasDerivAt_globalGeodesic_endpoint_chart p v 1
  have hchartη : HasDerivAt (fun t => extChartAt (𝓡 n) (γ 1) (η t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1) 1 := by
    rw [hpos]
    exact S.hasDerivAt_globalGeodesic_endpoint_chart p w 1
  have hgerm := hγ.eq_nhds_on_of_initial_data hη
    (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
    (t₀ := 1) (mem_univ 1) (γ 1) (mem_extChartAt_source (γ 1)) hpos
    (hchartγ.deriv.trans (hv.trans hchartη.deriv.symm))
  have hder := ((hgerm 0 (mem_univ 0)).fun_comp (extChartAt (𝓡 n) p)).deriv_eq
  exact ((S.metric.globalGeodesic_spec S.complete p v).2.2.deriv.symm.trans
    hder).trans (S.metric.globalGeodesic_spec S.complete p w).2.2.deriv

theorem globalExponential_surjective
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M) :
    Function.Surjective (S.metric.globalExponential S.complete p) := by
  intro q
  obtain ⟨ε, hε, γ, hγ, hp, hq, _⟩ :=
    S.metric.exists_minimizing_geodesic_of_metricComplete S.complete p q
  have hzero : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hchart := (hγ.hasDerivAt_chart_at hzero p
    (by rw [hp]; exact mem_extChartAt_source p)).1
  refine ⟨deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0, ?_⟩
  rw [S.metric.globalExponential_eq_endpoint S.complete p _
    (fun t ht => hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hp hchart]
  exact hq

theorem radial_exponential_flat_pullback
    (S : FlatShrinkingPotentialData (n := n) (M := M)) (p : M)
    {R : ℝ} (hR : 0 < R) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ e : EuclideanSpace ℝ (Fin n) → M,
        (∀ v w, S.metric.pullbackCoefficients
          (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p) (L v) (L w) =
          inner ℝ v w) ∧
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
        HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
          L.toContinuousLinearMap 0 ∧
        (∀ v ∈ Metric.ball 0 R,
          S.metric.pullbackCoefficients e v = innerSL ℝ) := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    S.metric.exists_orthonormal_radial_exponential_of_metricComplete
      S.complete p hR
  refine ⟨L, e, hL, he, he0, hed, ?_⟩
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 R := by
    simpa [Metric.mem_ball] using hR
  have hnorm : ∀ u w, S.metric.pullbackCoefficients e 0 u w = inner ℝ u w :=
    S.metric.pullbackCoefficients_zero_of_orthonormal p
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds h0)) he0 hed hL
  intro v hv
  apply S.metric.pullbackCoefficients_eq_innerSL_of_flat_radial S.connection
    he hnorm (fun z hz => (hgeo z hz).1) hv
  · intro t ht
    exact S.flat (e (t • v))
  · exact fun t ht => ((hgeo v hv).2 t ht).1

theorem weighted_volume_of_smooth_isometry
    (S : FlatShrinkingPotentialData (n := n) (M := M))
    (e : Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hinner : ∀ (x : EuclideanSpace ℝ (Fin n))
      (u v : TangentSpace (𝓡 n) x),
      (RiemannianMetric.euclideanMetric n).inner x u v =
        S.metric.inner (e x)
          (mfderiv (𝓡 n) (𝓡 n) e x u)
          (mfderiv (𝓡 n) (𝓡 n) e x v))
    (hpotential : ∀ x : EuclideanSpace ℝ (Fin n),
      S.potential (e x) = ‖x‖ ^ 2 / (4 * S.tau)) :
    ∫ y, S.tau ^ (-(n : ℝ) / 2) * Real.exp (-S.potential y)
        ∂S.metric.volumeMeasure = (4 * Real.pi) ^ ((n : ℝ) / 2) := by
  let gE := RiemannianMetric.euclideanMetric n
  have hed : ∀ x y, S.metric.edist (e x) (e y) = gE.edist x y := by
    intro x y
    exact (RiemannianMetric.edist_diffeomorph gE S.metric e hinner x y).symm
  let F : M → ℝ := fun y => S.tau ^ (-(n : ℝ) / 2) * Real.exp (-S.potential y)
  have htransport := RiemannianMetric.integral_comp_equiv_volumeMeasure
    gE S.metric (e : EuclideanSpace ℝ (Fin n) ≃ M) hed F
  have hsource : (∫ x, F (e x) ∂gE.volumeMeasure) = ∫ x, F (e x) := by
    rw [RiemannianMetric.euclideanMetric_volumeMeasure]
  calc
    (∫ y, F y ∂S.metric.volumeMeasure) =
        ∫ x, F (e x) ∂gE.volumeMeasure := htransport.symm
    _ = ∫ x, F (e x) := hsource
    _ = (4 * Real.pi) ^ ((n : ℝ) / 2) := by
      simp_rw [F, hpotential]
      rw [integral_const_mul]
      have htau : 0 < S.tau := S.tau_pos
      have hexp : (fun a : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-(‖a‖ ^ 2 / (4 * S.tau)))) =
          (fun a => Real.exp (-(1 / (4 * S.tau)) * ‖a‖ ^ 2)) := by
        funext a
        congr 1
        field_simp
      rw [hexp, GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := EuclideanSpace ℝ (Fin n))
        (by positivity : (0 : ℝ) < 1 / (4 * S.tau))]
      rw [show (-(n : ℝ) / 2) = -((n : ℝ) / 2) by ring]
      rw [Real.rpow_neg (by positivity)]
      field_simp [ne_of_gt htau]
      simp only [finrank_euclideanSpace, Fintype.card_fin]
      have hbase : Real.pi * 4 * S.tau = S.tau * (Real.pi * 4) := by ring
      rw [hbase, Real.mul_rpow (by positivity) (by positivity)]

theorem gaussian_rigidity
    (S : FlatShrinkingPotentialData (n := n) (M := M)) :
    ∃ e : Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      (∀ (x : EuclideanSpace ℝ (Fin n)) (u v : TangentSpace (𝓡 n) x),
        (RiemannianMetric.euclideanMetric n).inner x u v =
          S.metric.inner (e x)
            (mfderiv (𝓡 n) (𝓡 n) e x u)
            (mfderiv (𝓡 n) (𝓡 n) e x v)) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        S.potential (e x) = ‖x‖ ^ 2 / (4 * S.tau)) ∧
      (∫ y, S.tau ^ (-(n : ℝ) / 2) * Real.exp (-S.potential y)
          ∂S.metric.volumeMeasure) = (4 * Real.pi) ^ ((n : ℝ) / 2) := by
  classical
  obtain ⟨p, hp, hpgrad⟩ := S.exists_potential_zero
  obtain ⟨L, _, hL, _⟩ :=
    S.metric.exists_orthonormal_radial_exponential_of_metricComplete
      S.complete p (show (0 : ℝ) < 1 by norm_num)
  let e := fun v => S.metric.globalExponential S.complete p (L v)
  obtain ⟨he, hmetric⟩ :=
    S.metric.contMDiff_and_pullbackCoefficients_globalExponential_of_flat
      S.connection S.complete S.flat p L hL
  have hinj : Function.Injective e :=
    (S.globalExponential_injective p hp hpgrad).comp L.injective
  have hsurj : Function.Surjective e := (S.globalExponential_surjective p).comp L.surjective
  have hinner : ∀ (x : EuclideanSpace ℝ (Fin n)) (u v : TangentSpace (𝓡 n) x),
      S.metric.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x u)
        (mfderiv (𝓡 n) (𝓡 n) e x v) =
        (RiemannianMetric.euclideanMetric n).inner x u v := by
    intro x u v
    exact congrArg (fun B => B u v) (hmetric x)
  have hinverse : ContMDiff (𝓡 n) (𝓡 n) ∞ (Function.invFun e) := by
    have h := (RiemannianMetric.euclideanMetric n).contMDiffOn_invFun_of_injective_pullback_eq
      S.metric he hinj hinner
    rwa [hsurj.range_eq, contMDiffOn_univ] at h
  let d : Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞ :=
    { toFun := e
      invFun := Function.invFun e
      left_inv := Function.leftInverse_invFun hinj
      right_inv := Function.rightInverse_invFun hsurj
      contMDiff_toFun := he
      contMDiff_invFun := hinverse }
  have hdinner : ∀ (x : EuclideanSpace ℝ (Fin n)) (u v : TangentSpace (𝓡 n) x),
      (RiemannianMetric.euclideanMetric n).inner x u v =
        S.metric.inner (d x) (mfderiv (𝓡 n) (𝓡 n) d x u)
          (mfderiv (𝓡 n) (𝓡 n) d x v) := fun x u v => (hinner x u v).symm
  have hdpotential : ∀ x : EuclideanSpace ℝ (Fin n),
      S.potential (d x) = ‖x‖ ^ 2 / (4 * S.tau) := by
    intro x
    have hframe : S.metric.inner p (L x) (L x) = ‖x‖ ^ 2 := by
      have h := hL x x
      rw [S.metric.chartCoefficients_self, real_inner_self_eq_norm_sq] at h
      exact h
    have h := S.potential_globalGeodesic_eq_quadratic p (L x) 1
    change S.potential (S.metric.globalGeodesic S.complete p (L x) 1) = _
    rw [h, hp, hpgrad, hframe]
    simp only [map_zero, zero_apply, mul_zero, add_zero, zero_add, one_pow]
    ring
  exact ⟨d, hdinner, hdpotential, S.weighted_volume_of_smooth_isometry d hdinner hdpotential⟩

end FlatShrinkingPotentialData

end PoincareConjecture
