import PoincareConjecture.Proofs.M15.Thm8_10_ShortTail
import PoincareConjecture.Proofs.M15.Thm8_10_PathJoin
import PoincareConjecture.Statements.Ch06.ReducedVolume











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15




theorem exists_ball_reducedLength_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T taumax : ℝ)
    (htau : 0 < taumax) (hwindow : Icc (T - taumax) T ⊆ J)
    (hL : LGeodesicTheory F T taumax) (hV : ReducedVolumeTheory F T taumax)
    {c b : ℝ} (hc : 0 < c) (hcb : c < b) (hb : b < taumax)
    (g : RiemannianMetric n M) (p : M) {R C S : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hnorm : ∀ t ∈ Icc c b, ∀ x (v : TangentSpace (𝓡 n) x),
      (F.metric (T - t)).tangentNorm x v ≤ C * g.tangentNorm x v)
    (hscalar : ∀ t ∈ Icc c b, ∀ x,
      (F.connection (T - t)).scalarCurvature x ≤ S) :
    ∃ q0 : M, ∀ q ∈ g.ball q0 R,
      reducedLength F T p q b ≤
        (n : ℝ) / 2 + (S + (C * R / (b - c)) ^ 2) * (b - c) / 2 := by
  have hcmax : c ≤ taumax := (hcb.trans hb).le
  obtain ⟨q0, _, hq0⟩ := hV.minimum_bound p c hc (hcb.trans hb)
  obtain ⟨P, hP0, hPc, hPmin, hPvalue⟩ := hL.reduced_length_attained c hc hcmax p q0
  obtain ⟨RP⟩ := hL.regularized_geodesic 0 c le_rfl hc hcmax P
    (hL.euler_lagrange 0 c le_rfl hc hcmax P hPmin)
  have hPaction : backwardLLength F T 0 c P.curve ≤ (n : ℝ) * Real.sqrt c := by
    rw [hPvalue] at hq0
    have h := (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt c)).mp hq0
    nlinarith
  refine ⟨q0, ?_⟩
  intro q hq
  obtain ⟨Q, ⟨RQ⟩, hQc, hQb, hQaction⟩ := exists_backwardPath_short_tail
    F hM04 T taumax htau hwindow hc hcb hb g q0 q hR hC hS
      isClosed_closure.isCompact hq hnorm hscalar
  obtain ⟨U, hU0, hUb, hUmin, hUvalue⟩ :=
    hL.reduced_length_attained b (hc.trans hcb) hb.le p q
  have hsum : backwardLLength F T 0 b U.curve ≤
      backwardLLength F T 0 c P.curve + backwardLLength F T c b Q.curve := by
    apply le_of_forall_pos_le_add
    intro eta heta
    obtain ⟨W, hW0, hWb, hWa⟩ := exists_backwardPath_concat_approx
      F hM04 T taumax htau hwindow hc hcb hb P Q RP.path RQ
        (hPc.trans hQc.symm) eta heta
    exact (hUmin W (hW0.trans (hP0.trans hU0.symm))
      (hWb.trans (hQb.trans hUb.symm))).trans hWa
  have hprefix : backwardLLength F T 0 c P.curve ≤ (n : ℝ) * Real.sqrt b :=
    hPaction.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcb.le) (Nat.cast_nonneg n))
  rw [hUvalue]
  apply (div_le_iff₀ (mul_pos zero_lt_two (Real.sqrt_pos.mpr (hc.trans hcb)))).mpr
  nlinarith

end PoincareConjecture.Proofs.M15
