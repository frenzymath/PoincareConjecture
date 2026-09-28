import PoincareConjecture.Proofs.M09.LocalAdaptedField
import PoincareConjecture.Proofs.M09.PullbackCoordinate

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem field_chart_coordinates_smooth (p : M) (γ : ℝ → M)
    (P : ∀ t, TangentSpace (𝓡 n) (γ t)) (U : Set ℝ)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U)
    (hq : ∀ t ∈ U, γ t ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (fun t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t) (P t)) U := by
  have h := (tangentChartPhase_contMDiffOn p).comp hP (fun t ht ↦ hq t ht)
  exact h.contDiffOn.snd

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_coordinates_of_adapted_equation {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t))
    (K U : Set ℝ) (H : ParametricAlongCurveExtensionOn (n := n) K γ P)
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hq : ∀ t ∈ U, γ t ∈ (chartAt E p).source)
    (v : ℝ → E) (hv : ContDiffOn ℝ ∞ v U)
    (hrep : ∀ t ∈ K ∩ U, chartVectorField p (v t) (γ t) = P t)
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (heq : ∀ w : TangentSpace (𝓡 n) (γ s),
      (F.metric (T - s ^ 2)).inner (γ s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s) w =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) w) :
    HasDerivAt v (coordinateTransportOperator (squareChartMetric F T p)
      (s, (chartAt E p) (γ s)) (deriv (fun r ↦ (chartAt E p) (γ r)) s) (v s)) s := by
  let e := chartAt E p
  let y : ℝ → E := fun t ↦ e (γ t)
  let g := F.metric (T - s ^ 2)
  let L := (mfderiv (𝓡 n) (𝓡 n) e (γ s)).inverse
  let c := coordinateConnection (squareChartMetric F T p) (s, y s) (deriv y s) (v s)
  let B := coordinateTransportOperator (squareChartMetric F T p) (s, y s) (deriv y s) (v s)
  have hlinv : (mfderiv (𝓡 n) (𝓡 n) e (γ s)).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv (hq s hsU), rfl⟩
  have hpull : pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s =
      L (deriv v s + c) :=
    pullbackCovariantDerivative_eq_chart F T b hb hwindow p γ P K U H
      hU hγ hq v hv hrep s hs hsU hKd htime
  have hconn := squareChartConnection_eq F T b hb hwindow p s htime
    (y s) (e.map_source (hq s hsU)) (deriv y s) (v s)
  dsimp only [y] at hconn
  rw [e.left_inv (hq s hsU)] at hconn
  have href (w : E) : g.inner (γ s) (L (B + c)) (L w) =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) (L w) := by
    have h := squareChartTransport_pairing F T b hb hwindow p s htime
      (y s) (e.map_source (hq s hsU)) (deriv y s) (v s) w
    dsimp only [y] at h
    rw [e.left_inv (hq s hsU), ← hconn, hrep s ⟨hs, hsU⟩] at h
    change g.inner (γ s) (L B + L c) (L w) =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) (L w) at h
    simpa only [map_add] using h
  have hpair (w : E) : g.inner (γ s) (L (deriv v s - B)) (L w) = 0 := by
    have h1 := heq (L w)
    rw [hpull] at h1
    have h2 := href w
    change g.inner (γ s) (L (deriv v s + c)) (L w) = _ at h1
    simp only [map_add, add_apply] at h1 h2
    simp only [map_sub, sub_apply]
    linarith
  have hzero : L (deriv v s - B) = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos (γ s) (L (deriv v s - B)) hne)) (hpair (deriv v s - B))
  have hderiv : deriv v s = B := by
    apply sub_eq_zero.mp
    apply hlinv.inverse.injective
    exact hzero.trans L.map_zero.symm
  exact ((hv.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)).hasDerivAt.congr_deriv hderiv

end PoincareConjecture.Proofs.M09
