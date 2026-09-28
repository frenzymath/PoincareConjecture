import PoincareConjecture.Proofs.M47.TerminalSourceChartsEllipticity
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_LengthBarrier
import PoincareConjecture.Proofs.M44.Mathlib.PartialHomeomorphCompact
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics
import PoincareConjecture.Proofs.M01.NormalizationScaling







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

noncomputable def terminalSourceShiRadius (a ρ : ℝ) : ℝ := Real.sqrt a * (ρ / 4)

theorem terminalSourceShiRadius_pos {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    0 < terminalSourceShiRadius a ρ := by
  unfold terminalSourceShiRadius
  positivity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]



theorem terminalSourceCharts_compact_ball
    (h : RiemannianMetric 3 M) (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {R ρ a : ℝ} (hsource : Φ.source = Metric.ball 0 R)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R) (ha : 0 < a)
    (hlower : ∀ z ∈ Metric.closedBall 0 (2 * ρ), ∀ v,
      a * ‖v‖ ^ 2 ≤ h.pullbackCoefficients Φ z v v)
    {x : E} (hx : x ∈ Metric.ball 0 (3 * ρ / 2)) :
    IsCompact (closure (h.ball (Φ x) (terminalSourceShiRadius a ρ))) ∧
      h.ball (Φ x) (terminalSourceShiRadius a ρ) ⊆ Φ '' Metric.ball 0 R := by
  let V : Set E := Metric.ball x (ρ / 4)
  have hopenV : IsOpen V := Metric.isOpen_ball
  have hleft (z : E) (hz : z ∈ Φ.source) :
      Φ.symm.toPartialEquiv (Φ.toPartialEquiv z) = z := Φ.left_inv hz
  have hδ : 0 < ρ / 4 := by positivity
  have hcl : closure V ⊆ Metric.closedBall x (ρ / 4) :=
    closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  have htwo : closure V ⊆ Metric.closedBall 0 (2 * ρ) := by
    intro z hz
    have hd := dist_triangle z x 0
    have hz' : dist z x ≤ ρ / 4 := hcl hz
    have hx' : dist x 0 < 3 * ρ / 2 := hx
    change dist z 0 ≤ 2 * ρ
    linarith
  have hsub : closure V ⊆ Φ.source := by
    rw [hsource]
    exact htwo.trans (Metric.closedBall_subset_ball hρR)
  have hcompact : IsCompact (closure V) :=
    (isCompact_closedBall x (ρ / 4)).of_isClosed_subset isClosed_closure hcl
  let O : Set M := Φ '' V
  have hO : IsOpen O := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    Metric.isOpen_ball (subset_closure.trans hsub)
  have hc := Φ.toOpenPartialHomeomorph.image_closure_of_compact_buffer hcompact hsub
  have hf := Φ.toOpenPartialHomeomorph.image_frontier_of_compact_buffer
    Metric.isOpen_ball hcompact hsub
  change Φ '' closure V = closure O at hc
  change Φ '' frontier V = frontier O at hf
  have hOc : IsCompact (closure O) := by
    rw [← hc]
    exact hcompact.image_of_continuousOn (Φ.toOpenPartialHomeomorph.continuousOn.mono hsub)
  have htarget : closure O ⊆ Φ.target := by
    rw [← hc]
    rintro _ ⟨z, hz, rfl⟩
    exact Φ.map_source (hsub hz)
  have hxV : x ∈ V := Metric.mem_ball_self hδ
  have hxs : x ∈ Φ.source := hsub (subset_closure hxV)
  let kE := m01RescaledMetric (RiemannianMetric.euclideanMetric 3) a ha
  have hsmooth : ∀ y ∈ closure O, ContMDiffAt (𝓡 3) (𝓡 3) ∞ Φ.symm y :=
    fun y hy => Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds (htarget hy))
  have hmetric : ∀ y ∈ closure O, ∀ v : TangentSpace (𝓡 3) y,
      kE.inner (Φ.symm y) (mfderiv (𝓡 3) (𝓡 3) Φ.symm y v)
        (mfderiv (𝓡 3) (𝓡 3) Φ.symm y v) ≤ h.inner y v v := by
    intro y hy v
    have hyt := htarget hy
    have he : Φ.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
      ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
    have hd := congrArg (fun A => A v) (he.comp_symm_deriv hyt)
    have hpre : Φ.symm y ∈ closure V := by
      rw [← hc] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa only [hleft z (hsub hz)] using hz
    have hb := hlower (Φ.symm y) (htwo hpre) (mfderiv (𝓡 3) (𝓡 3) Φ.symm y v)
    change a * ‖mfderiv (𝓡 3) (𝓡 3) Φ.symm y v‖ ^ 2 ≤
      h.inner (Φ (Φ.symm y))
        (mfderiv (𝓡 3) (𝓡 3) Φ (Φ.symm y) (mfderiv (𝓡 3) (𝓡 3) Φ.symm y v))
        (mfderiv (𝓡 3) (𝓡 3) Φ (Φ.symm y) (mfderiv (𝓡 3) (𝓡 3) Φ.symm y v)) at hb
    change mfderiv (𝓡 3) (𝓡 3) Φ (Φ.symm y)
      (mfderiv (𝓡 3) (𝓡 3) Φ.symm y v) = v at hd
    have hright : Φ.toPartialEquiv (Φ.symm.toPartialEquiv y) = y := Φ.right_inv hyt
    rw [hd, hright] at hb
    simpa only [kE, m01RescaledMetric_inner, RiemannianMetric.euclideanMetric_inner,
      real_inner_self_eq_norm_sq] using hb
  have hboundary : ∀ y ∈ frontier O,
      ENNReal.ofReal (terminalSourceShiRadius a ρ) ≤ kE.edist (Φ.symm (Φ x)) (Φ.symm y) := by
    intro y hy
    rw [← hf] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hznot : z ∉ V := by simpa only [hopenV.interior_eq] using hz.2
    have hdist : ρ / 4 ≤ dist x z := by
      simpa only [V, Metric.mem_ball, dist_comm, not_lt] using hznot
    rw [hleft x hxs, hleft z (hsub hz.1)]
    change ENNReal.ofReal (Real.sqrt a * (ρ / 4)) ≤
      (m01RescaledMetric (RiemannianMetric.euclideanMetric 3) a ha).edist x z
    rw [m01RescaledMetric_edist, RiemannianMetric.euclideanMetric_edist,
      edist_dist, ENNReal.ofReal_mul (Real.sqrt_nonneg a)]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hdist) _
  have hball := h.ball_subset_of_inverse_length_barrier kE Φ.symm hO
    (mem_image_of_mem Φ hxV) hsmooth hmetric hboundary
  refine ⟨h.isCompact_closure_ball_of_inverse_length_barrier kE Φ.symm hO hOc
    (mem_image_of_mem Φ hxV) hsmooth hmetric hboundary, ?_⟩
  apply hball.trans (image_mono ?_)
  exact (subset_closure.trans hsub).trans (by rw [hsource])

end PoincareConjecture.M47
