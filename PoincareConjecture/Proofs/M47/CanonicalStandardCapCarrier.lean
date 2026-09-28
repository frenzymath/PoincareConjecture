import PoincareConjecture.Proofs.M47.CanonicalStandardMetricBounds
import PoincareConjecture.Proofs.M47.TerminalCurvatureCapLocalization
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalar
import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Proofs.M36.StandardBalls










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_standard_cap_initial_ball {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta C c R : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1)
    (hC : 0 < C) (hc : 0 < c) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ R < A ∧ ∀ s ∈ Icc 0 theta,
      ∀ N : CapCertificate (standard.flow.metric s),
        N.connection = standard.flow.connection s → N.cap_constant ≤ C →
      ∀ x ∈ N.core,
        c ≤ (standard.flow.connection s).scalarCurvature x →
        g0.metric.edist 0 x ≤ ENNReal.ofReal R →
        IsCompact (closure N.carrier) ∧ closure N.carrier ⊆ g0.metric.ball 0 A := by
  obtain ⟨Lambda, hLambda, hmetric⟩ :=
    exists_standard_initial_distance_factor standard htheta0 htheta
  let d := C * c ^ (-1 / 2 : ℝ)
  have hd : 0 < d := mul_pos hC (Real.rpow_pos_of_pos hc _)
  let r := R + Lambda * d
  have hr : 0 < r := add_pos_of_nonneg_of_pos hR (mul_pos hLambda hd)
  refine ⟨r + 1, by linarith, ?_, ?_⟩
  · dsimp only [r]
    linarith [mul_pos hLambda hd]
  intro s hs N hconnection hconstant x hx hscalar hxR
  have hscalar' : c ≤ N.connection.scalarCurvature x := by
    simpa only [hconnection] using hscalar
  have hball := PoincareConjecture.M47.terminalCurvature_cap_carrier_subset_ball
    N hconstant hc hx hscalar'
  have hcarrier : N.carrier ⊆ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal r} := by
    intro y hy
    have hyball : (standard.flow.metric s).edist x y < ENNReal.ofReal d := hball hy
    calc
      g0.metric.edist 0 y ≤ g0.metric.edist 0 x + g0.metric.edist x y :=
        M36.metric_edist_triangle g0.metric 0 x y
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal Lambda * (standard.flow.metric s).edist x y :=
        add_le_add hxR (hmetric s hs x y)
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal Lambda * ENNReal.ofReal d :=
        add_le_add le_rfl (mul_le_mul' le_rfl hyball.le)
      _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul hLambda.le, ← ENNReal.ofReal_add hR
          (mul_pos hLambda hd).le]
  have hclosed : IsClosed {y | g0.metric.edist 0 y ≤ ENNReal.ofReal r} :=
    isClosed_le ((M36.metric_edist_continuous g0.metric).comp
      (continuous_const.prodMk continuous_id)) continuous_const
  have hclosure := closure_minimal hcarrier hclosed
  refine ⟨(M36.standard_closed_ball_compact g0 hr.le).of_isClosed_subset
    isClosed_closure hclosure, ?_⟩
  intro y hy
  exact (hclosure hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < r + 1)).mpr
    (by linarith))



theorem exists_standard_cap_uniform_initial_ball {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta C R : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (hC : 0 < C) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ R < A ∧ ∀ s ∈ Icc 0 theta,
      ∀ N : CapCertificate (P.standard_cap.flow.metric s),
        N.connection = P.standard_cap.flow.connection s → N.cap_constant ≤ C →
      ∀ x ∈ N.core, g0.metric.edist 0 x ≤ ENNReal.ofReal R →
        IsCompact (closure N.carrier) ∧ closure N.carrier ⊆ g0.metric.ball 0 A := by
  obtain ⟨c, hc, hrate⟩ := (Classical.choice P.standard_cap_uniqueness).scalar_lower_bound
  obtain ⟨A, hA, hRA, hcaps⟩ := exists_standard_cap_initial_ball
    P.standard_cap htheta0 htheta hC hc hR
  refine ⟨A, hA, hRA, ?_⟩
  intro s hs N hconnection hconstant x hx hxR
  have htime : s ∈ Ico 0 P.standard_cap.flow.base.lifetime := by
    rw [P.standard_cap.lifetime_one]
    exact ⟨hs.1, hs.2.trans_lt htheta⟩
  have hden : 0 < 1 - s := by linarith [hs.2]
  have hfloor : c ≤ (P.standard_cap.flow.connection s).scalarCurvature x := by
    apply le_trans _ (hrate s htime x)
    apply (le_div_iff₀ hden).mpr
    nlinarith [hc, hs.1]
  exact hcaps s hs N hconnection hconstant x hx hfloor hxR

end PoincareConjecture.Proofs.M47
