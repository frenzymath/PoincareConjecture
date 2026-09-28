import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.BallClosure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]



theorem ball_subset_ball_of_tangentNorm_le_on_closedBall
    (g h : RiemannianMetric n M) (p : M) {r R C : ℝ}
    (_hR : 0 < R) (hC : 0 < C) (hrR : C * r ≤ R)
    (hbound : ∀ x, g.edist p x ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace (𝓡 n) x, g.tangentNorm x v ≤ C * h.tangentNorm x v) :
    h.ball p r ⊆ g.ball p R := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  intro q hq
  by_contra hqg
  have hqR : ENNReal.ofReal R ≤ g.edist p q := le_of_not_gt hqg
  obtain ⟨γ, h0, h1, hγ, hlen⟩ :
      ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ ∧
        h.pathELength γ 0 1 < ENNReal.ofReal r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hq zero_lt_one
    exact ⟨γ, h0, h1, hγ, hlen⟩
  have hd : Continuous (fun s : ℝ => g.edist p (γ s)) :=
    continuous_const.edist hγ.continuous
  have hzero : g.edist p (γ 0) = 0 := by
    rw [h0]
    exact Manifold.riemannianEDist_self
  have hroot : (Icc (0 : ℝ) 1 ∩ {s | g.edist p (γ s) = ENNReal.ofReal R}).Nonempty := by
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc zero_le_one hd.continuousOn
      (show ENNReal.ofReal R ∈ Icc (g.edist p (γ 0)) (g.edist p (γ 1)) from by
        rw [hzero, h1]
        exact ⟨bot_le, hqR⟩)
    exact ⟨s, hs, heq⟩
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ∩
      {s | g.edist p (γ s) = ENNReal.ofReal R}) :=
    isCompact_Icc.inter_right (isClosed_eq hd continuous_const)
  obtain ⟨u, hu, humin⟩ := hcompact.exists_isMinOn hroot continuous_id.continuousOn
  have hstay : ∀ s ∈ Icc (0 : ℝ) u, g.edist p (γ s) ≤ ENNReal.ofReal R := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hsu
    · exact hu.2.le
    · by_contra hbad
      have hRs : ENNReal.ofReal R ≤ g.edist p (γ s) := (lt_of_not_ge hbad).le
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc hs.1 hd.continuousOn
        (show ENNReal.ofReal R ∈ Icc (g.edist p (γ 0)) (g.edist p (γ s)) from by
          rw [hzero]
          exact ⟨bot_le, hRs⟩)
      have huv := humin ⟨⟨hv.1, hv.2.trans (hs.2.trans hu.1.2)⟩, hveq⟩
      exact not_le_of_gt (hv.2.trans_lt hsu) huv
  have hlength := h.pathELength_le_of_tangentNorm_le g γ 0 u C hC.le
    (fun s hs => hbound (γ s) (hstay s hs))
  have hgdist : g.edist p (γ u) ≤ g.pathELength γ 0 u :=
    Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn h0 rfl hu.1.1
  have hlengthmono : h.pathELength γ 0 u ≤ h.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_mono le_rfl hu.1.2
  have hstrict : ENNReal.ofReal C * h.pathELength γ 0 u <
      ENNReal.ofReal (C * r) := by
    rw [ENNReal.ofReal_mul hC.le]
    exact ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
      ENNReal.ofReal_ne_top (hlengthmono.trans_lt hlen)
  have hcontr := ((hgdist.trans hlength).trans_lt hstrict).trans_le
    (ENNReal.ofReal_le_ofReal hrR)
  exact (not_lt_of_ge hu.2.ge) hcontr



theorem isCompact_closure_ball_of_tangentNorm_le_on_closedBall
    (g h : RiemannianMetric n M) (p : M) {r R C : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hrR : C * r ≤ R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hbound : ∀ x, g.edist p x ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace (𝓡 n) x, g.tangentNorm x v ≤ C * h.tangentNorm x v) :
    IsCompact (closure (h.ball p r)) := by
  exact hcompact.of_isClosed_subset isClosed_closure (closure_mono
    (g.ball_subset_ball_of_tangentNorm_le_on_closedBall h p hR hC hrR hbound))

end PoincareConjecture.RiemannianMetric
