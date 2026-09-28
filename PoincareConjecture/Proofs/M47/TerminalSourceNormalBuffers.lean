import PoincareConjecture.Proofs.M47.TerminalSourceNormalScaling
import PoincareConjecture.Proofs.M47.TerminalSourceNormalTransfer
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N]

theorem terminalSourceNormal_physical_ball_volume
    (g : RiemannianMetric 3 M) (gphys : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = Q * gphys.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p : M) (r : ℝ) (hcover : gphys.ball (e p) (r / Real.sqrt Q) ⊆ e.target) :
    calibratedMetricVolume g (g.ball p r) = ENNReal.ofReal (Real.sqrt Q ^ 3) *
      calibratedMetricVolume gphys (gphys.ball (e p) (r / Real.sqrt Q)) := by
  let h : RiemannianMetric 3 N := M13.scaleSmoothMetric gphys Q hQ
  have hm (x : M) (v w : TangentSpace (𝓡 3) x) :
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := hmetric x v w
  have hball : h.ball (e p) r = gphys.ball (e p) (r / Real.sqrt Q) :=
    terminalSourceNormal_scaled_ball gphys hQ (e p) r
  rw [terminalSourceNormal_ball_volume g h e hsource hm p r (hball.symm ▸ hcover), hball]
  exact terminalSourceNormal_scaled_volume gphys hQ _

theorem terminalSourceNormal_physical_buffers
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (gphys : RiemannianMetric 3 N) (Dphys : LeviCivitaData gphys)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    {Q R r K v : ℝ} (hQ : 0 < Q) (hR : 0 < R) (hrR : r ≤ R)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = Q * gphys.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (hnorm : ∀ x, D.curvatureTensorNorm x = Dphys.curvatureTensorNorm (e x) / Q)
    (p0 : M) (hcompact : IsCompact (univ : Set N))
    (hcover : gphys.ball (e p0) (6 * R / Real.sqrt Q) ⊆ e.target)
    (hcurv : ∀ x ∈ gphys.ball (e p0) (5 * R / Real.sqrt Q),
      Dphys.curvatureTensorNorm x ≤ K * Q)
    (hvol : ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤
      calibratedMetricVolume gphys (gphys.ball (e p0) (r / Real.sqrt Q))) :
    IsCompact (closure (g.ball p0 (5 * R))) ∧
      (∀ x ∈ g.ball p0 (5 * R), D.curvatureTensorNorm x ≤ K) ∧
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p0 r) := by
  let h : RiemannianMetric 3 N := M13.scaleSmoothMetric gphys Q hQ
  have hm (x : M) (v w : TangentSpace (𝓡 3) x) :
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := hmetric x v w
  have hball (s : ℝ) : h.ball (e p0) s = gphys.ball (e p0) (s / Real.sqrt Q) :=
    terminalSourceNormal_scaled_ball gphys hQ (e p0) s
  have hcover' : h.ball (e p0) (6 * R) ⊆ e.target := (hball _).symm ▸ hcover
  have hp0 : e p0 ∈ h.ball (e p0) (R / 2) := by
    change h.edist (e p0) (e p0) < ENNReal.ofReal (R / 2)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hcl : closure (h.ball (e p0) (5 * R)) ⊆ h.ball (e p0) (6 * R) :=
    h.closure_ball_subset_ball_of_margin (by positivity : 0 ≤ R / 2)
      (by positivity) (by linarith) hp0
  refine ⟨terminalSourceNormal_compact_ball g h e hsource hm p0 (5 * R)
    (hcompact.of_isClosed_subset isClosed_closure (subset_univ _)) (hcl.trans hcover'), ?_, ?_⟩
  · intro x hx
    have hmem : e x ∈ h.ball (e p0) (5 * R) :=
      (terminalSourceNormal_edist_le g h e hsource hm p0 x).trans_lt hx
    rw [hnorm]
    exact (div_le_iff₀ hQ).mpr (hcurv (e x) (hball _ ▸ hmem))
  · have hcr : h.ball (e p0) r ⊆ e.target := fun x hx =>
      hcover' (hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith : r ≤ 6 * R)))
    have hfloor := terminalSourceNormal_scaled_ball_volume_lower gphys hQ (e p0) hvol
    rw [← terminalSourceNormal_ball_volume g h e hsource hm p0 r hcr] at hfloor
    simpa only [Proofs.M15.calibratedMetricVolume_eq_volumeMeasure] using hfloor

end PoincareConjecture.M47
