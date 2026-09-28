import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FixedCoordinateFlowLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalChartJetBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.BackwardMetricComparison
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.MixedBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateGerms
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetsOfAmbient
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_fixedCoordinateFlowLimit_of_normal_charts
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {tau R rho K : ℝ} (htau : 0 < tau) (hrho : 0 < rho)
    (hrhoR : 2 * rho < R) (hK : 0 ≤ K)
    (F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0)) (p : ∀ k, M k)
    (L : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Phi : ∀ k, PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    (hsource : ∀ k, (Phi k).source = Metric.ball 0 R)
    (hzero : ∀ k, Phi k 0 = p k)
    (hL : ∀ k v w, ((F k).metric 0).pullbackCoefficients
      (extChartAt (𝓡 n) (p k)).symm (extChartAt (𝓡 n) (p k) (p k))
        (L k v) (L k w) = inner ℝ v w)
    (hderivative : ∀ k, HasFDerivAt (fun w => extChartAt (𝓡 n) (p k) (Phi k w))
      (L k).toContinuousLinearMap 0)
    (hgeodesic : ∀ k w, w ∈ Metric.ball 0 R →
      ((F k).metric 0).IsGeodesicOn (fun s : ℝ => Phi k (s • w))
        {s : ℝ | s • w ∈ Metric.ball 0 R})
    (hspeed : ∀ k w, w ∈ Metric.ball 0 R → ∀ s ∈ Icc (0 : ℝ) 1,
      ((F k).metric 0).tangentNorm (Phi k (s • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun a : ℝ => Phi k (a • w)) s 1) = ‖w‖)
    (hterminal : ∀ k x, x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * rho) →
      ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((F k).metric 0).pullbackCoefficients (Phi k) x v v ∧
        ((F k).metric 0).pullbackCoefficients (Phi k) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    (hcurv : ∀ k t, t ∈ Icc (-tau) 0 → ∀ x : M k,
      ((F k).connection t).curvatureTensorNorm x ≤ K)
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hjets : ∀ m k t, t ∈ Icc (-tau) 0 → ∀ x ∈ Metric.ball 0 R,
      ((F k).connection t).curvatureDerivativeNorm m (Phi k x) ≤ C m) :
    letI : Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) rho) :=
      ⟨⟨0, Metric.mem_ball_self hrho⟩⟩
    Nonempty (FixedCoordinateFlowLimit F (Metric.ball 0 rho) Metric.isOpen_ball
      (fun k x => Phi k x)) := by
  classical
  let V : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 rho
  let Vbar : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 (2 * rho)
  let U0 : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 R
  let hV : IsOpen V := Metric.isOpen_ball
  let : Nonempty V := ⟨⟨0, Metric.mem_ball_self hrho⟩⟩
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hVbarU : Vbar ⊆ U0 := Metric.closedBall_subset_ball hrhoR
  have hVVbar : V ⊆ Vbar :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hVU : V ⊆ U0 := hVVbar.trans hVbarU
  let e : ∀ k, V → M k := fun k x => Phi k x
  let param := fun k => chartParametrization (fun _ : Unit => V) (fun _ => hV)
    (i := ()) (e k)
  have he : ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k) := by
    intro k x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) V hV ∞ x).comp (𝓡 n) (M k)
      ((Phi k).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ ((hsource k).symm ▸ hVU x.property))
  have hparam (k : ℕ) : EqOn (param k) (Phi k) V := by
    intro x hx
    exact chartParametrization_apply (fun _ : Unit => V) (fun _ => hV) (e k) ⟨x, hx⟩
  have hcoeff (k : ℕ) (t : ℝ) :
      EqOn (((F k).metric t).pullbackCoefficients (param k))
        (((F k).metric t).pullbackCoefficients (Phi k)) V := by
    intro x hx
    exact ((F k).metric t).pullbackCoefficients_eq_of_eventuallyEq
      (Filter.mem_of_superset (hV.mem_nhds hx) (hparam k))
  let alpha := Real.exp (-2 * (n : ℝ) * K * tau) * (1 / 4)
  let beta := Real.exp (2 * (n : ℝ) * K * tau) * (9 / 4)
  have ha : 0 < alpha := mul_pos (Real.exp_pos _) (by norm_num)
  have hb : 0 ≤ beta := (mul_pos (Real.exp_pos _) (by norm_num)).le
  have hell : ∀ k t, t ∈ Icc (-tau) 0 → ∀ x ∈ Vbar, ∀ v,
      alpha * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients (Phi k) x v v ∧
        ((F k).metric t).pullbackCoefficients (Phi k) x v v ≤ beta * ‖v‖ ^ 2 := by
    intro k t ht x hx v
    exact backward_pullback_ellipticity (F k) htau hK (Phi k) x
      (fun s hs => hcurv k s hs _) (hterminal k x hx) ht v
  have hsmooth (k : ℕ) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Phi k) U0 := by
    simpa only [hsource k] using (Phi k).contMDiffOn
  have hinvertible (k : ℕ) (x) (hx : x ∈ U0) :
      (mfderiv (𝓡 n) (𝓡 n) (Phi k) x).IsInvertible :=
    ⟨((Phi k).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      ((hsource k).symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hinit (m : ℕ) : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ᶠ k in atTop, ∀ x ∈ Vbar,
      ‖iteratedFDeriv ℝ m (((F k).metric 0).pullbackCoefficients (Phi k)) x‖ ≤ Z := by
    obtain ⟨Z, hZ, hbound⟩ := exists_uniform_normal_chart_metric_jet_bound
      n m (by linarith : 0 < 2 * rho) hrhoR C hC
    refine ⟨Z, hZ, Eventually.of_forall fun k => ?_⟩
    exact hbound ((F k).metric 0) ((F k).connection 0) (p k) (L k) (Phi k)
      (hsource k) (hzero k) (hL k) (hderivative k) (hgeodesic k) (hspeed k)
      (fun m _ x hx => hjets m k 0 ⟨by linarith, le_rfl⟩ x hx)
  have hmixed := eventually_within_bounds_closed_backward_of_curvature atTop htau F
    (fun _ => U0) (fun _ => Vbar) (fun k => Phi k)
    (fun _ => Metric.isOpen_ball) (fun _ => hVbarU) hsmooth hinvertible ha hb
    (Eventually.of_forall hell)
    (fun m => ⟨C m, hC m, Eventually.of_forall fun k t ht x hx =>
      hjets m k t (Ioo_subset_Icc_self ht) x (hVbarU hx)⟩) hinit
  apply exists_fixedCoordinateFlowLimit_of_within_bounds F V hV e htau
    (convex_ball _ _) he ha
  · refine Eventually.of_forall fun k t ht x hx v => ?_
    rw [hcoeff k t hx]
    exact (hell k t ht x (hVVbar hx) v).1
  · intro K0 _hK0 hsub m
    obtain ⟨Z, _hZ, hbound⟩ := hmixed m
    refine ⟨Z, hbound.mono fun k hk z hz => ?_⟩
    have heq : EqOn
        (fun z => ((F k).metric z.1).pullbackCoefficients (param k) z.2)
        (fun z => ((F k).metric z.1).pullbackCoefficients (Phi k) z.2)
        (Icc (-tau) 0 ×ˢ V) := fun z hz => hcoeff k z.1 hz.2
    rw [(heq.iteratedFDerivWithin m) (hsub hz),
      iteratedFDerivWithin_prod_eq_of_isOpen
        (fun z => ((F k).metric z.1).pullbackCoefficients (Phi k) z.2) m hV
        Metric.isOpen_ball (hsub hz).2 (hVU (hsub hz).2)]
    exact hk z ⟨(hsub hz).1, hVVbar (hsub hz).2⟩

end PoincareConjecture.M28
