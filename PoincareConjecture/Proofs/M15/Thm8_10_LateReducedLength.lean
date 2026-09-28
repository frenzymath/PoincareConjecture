import PoincareConjecture.Proofs.M15.Thm8_10_MinimumBall
import PoincareConjecture.Proofs.M15.Thm8_10_DoublingTime
import PoincareConjecture.Proofs.M15.Prop8_2_CurvatureContractions
import PoincareConjecture.Proofs.M04.LocalMetricComparison










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15




theorem exists_compact_late_reducedLength_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ l0 : ℝ, 0 < l0 ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T3Space M] [MeasurableSpace M] [BorelSpace M]
        [CompactSpace M] [ConnectedSpace M]
        (T : ℝ) (_hT : 0 < T) (F : RicciFlow 3 M (Icc 0 T)),
        (∀ q, (F.connection 0).curvatureTensorNorm q ≤ 1) →
        ∀ (t0 : ℝ), t0 ≤ T → 1 / (32 * (3 : ℝ) ^ 6) ≤ t0 →
        ∀ (p : M) (_hL : LGeodesicTheory F t0 t0)
          (_hV : ReducedVolumeTheory F t0 t0),
        ∃ q0 : M, ∀ q ∈ (F.metric 0).ball q0 1,
          reducedLength F t0 p q (t0 - 1 / (32 * (3 : ℝ) ^ 6) / 4) ≤ l0 := by
  let delta : ℝ := 1 / (32 * (3 : ℝ) ^ 6)
  let C : ℝ := Real.exp (6 * delta)
  have hdelta : 0 < delta := by norm_num [delta]
  have hC : 0 < C := Real.exp_pos _
  refine ⟨3 / 2 + (18 + (C / (delta / 4)) ^ 2) * (delta / 4) / 2, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ T hT F hinit t0 ht0 hlate p hL hV
  change delta ≤ t0 at hlate
  let c := t0 - delta / 2
  let b := t0 - delta / 4
  have ht0pos : 0 < t0 := hdelta.trans_le hlate
  have hc : 0 < c := sub_pos.mpr ((half_lt_self hdelta).trans_le hlate)
  have hcb : c < b := by dsimp only [c, b]; linarith
  have hb : b < t0 := by dsimp only [b]; linarith
  have hwindow : Icc (t0 - t0) t0 ⊆ Icc 0 T := by
    intro s hs
    exact ⟨by simpa only [sub_self] using hs.1, hs.2.trans ht0⟩
  have hphys (t : ℝ) (ht : t ∈ Icc c b) : t0 - t ∈ Icc 0 (min T delta) := by
    dsimp only [c, b] at ht
    have hlo : delta / 4 ≤ t0 - t := by linarith only [ht.2]
    have hhi : t0 - t ≤ delta / 2 := by linarith only [ht.1]
    exact ⟨(div_nonneg hdelta.le (by norm_num)).trans hlo,
      le_min (hhi.trans ((half_le_self hdelta.le).trans (hlate.trans ht0)))
        (hhi.trans (half_le_self hdelta.le))⟩
  have hcurv (s : ℝ) (hs : s ∈ Icc 0 (min T delta)) (x : M) :
      (F.connection s).curvatureTensorNorm x ≤ 2 :=
    compact_curvature_le_two_of_initial_bound (by decide) hT F hinit s hs x
  have hnorm (t : ℝ) (ht : t ∈ Icc c b) (x : M) (v : TangentSpace (𝓡 3) x) :
      (F.metric (t0 - t)).tangentNorm x v ≤ C * (F.metric 0).tangentNorm x v := by
    have hs := hphys t ht
    have hn := M04.tangentNorm_comparison_at_of_curvature_bound F
      (show 0 ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
      (show t0 - t ∈ Icc 0 T from ⟨hs.1, hs.2.trans (min_le_left _ _)⟩)
      hs.1 (by norm_num : (0 : ℝ) ≤ 2) x
      (fun s hst => hcurv s ⟨hst.1, hst.2.trans hs.2⟩ x) v
    apply hn.2.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    change (3 : ℝ) * 2 * (t0 - t - 0) ≤ 6 * delta
    linarith [hs.2.trans (min_le_right T delta)]
  have hscalar (t : ℝ) (ht : t ∈ Icc c b) (x : M) :
      (F.connection (t0 - t)).scalarCurvature x ≤ 18 := by
    calc
      _ ≤ |(F.connection (t0 - t)).scalarCurvature x| := le_abs_self _
      _ ≤ (3 : ℝ) ^ 2 * (F.connection (t0 - t)).curvatureTensorNorm x :=
        abs_scalarCurvature_le_curvatureTensorNorm _ _
      _ ≤ (3 : ℝ) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (hcurv _ (hphys t ht) x) (sq_nonneg _)
      _ = 18 := by norm_num
  obtain ⟨q0, hq0⟩ := exists_ball_reducedLength_bound F hM04 t0 t0 ht0pos hwindow
    hL hV hc hcb hb (F.metric 0) p (by norm_num : (0 : ℝ) < 1) hC.le
      (by norm_num : (0 : ℝ) ≤ 18) hnorm hscalar
  refine ⟨q0, ?_⟩
  intro q hq
  have hbc : b - c = delta / 4 := by dsimp only [b, c]; ring
  simpa only [hbc, mul_one, Nat.cast_ofNat] using hq0 q hq

end PoincareConjecture.Proofs.M15
