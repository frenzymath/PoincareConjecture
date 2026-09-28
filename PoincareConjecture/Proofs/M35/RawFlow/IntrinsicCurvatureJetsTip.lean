import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.AxisDivisionJets
import PoincareConjecture.Proofs.M35.RadialGauge.ScalarJetContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.EvenRadialCompactJets
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
  {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime)

include hT hTlt

theorem raw_intrinsic_jet_continuous_subtype (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (rawWarpingRadius P G hrotation p.1.1) p.2) :=
  (raw_intrinsic_jet_continuousOn_slab G P hrotation j hT hTlt).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun p => ⟨p.1.2, mem_univ _⟩)

theorem raw_intrinsic_quotient_jet_continuous_subtype (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (axisDivision (rawWarpingRadius P G hrotation p.1.1)) p.2) := by
  apply RadialGauge.axisDivision_jet_continuous
    (f := fun t : Icc (0 : ℝ) T => rawWarpingRadius P G hrotation t.1) (j := j)
  · intro t
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact intrinsicWarpingRadius_contDiff _ _ _
  · exact raw_intrinsic_jet_continuous_subtype P G hrotation hT hTlt (j + 1)

theorem raw_intrinsic_log_jet_continuous_subtype (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (fun r => Real.log
        (axisDivision (rawWarpingRadius P G hrotation p.1.1) r)) p.2) := by
  have hs (t : Icc (0 : ℝ) T) :
      ContDiff ℝ ∞ (axisDivision (rawWarpingRadius P G hrotation t.1)) := by
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact intrinsicWarpingQuotient_contDiff _ _ _
  have hp (t : Icc (0 : ℝ) T) (r : ℝ) :
      axisDivision (rawWarpingRadius P G hrotation t.1) r ≠ 0 := by
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact (intrinsicWarpingQuotient_pos _ _ _ r).ne'
  exact RadialGauge.scalar_jets_continuous_log hs hp
    (raw_intrinsic_quotient_jet_continuous_subtype P G hrotation hT hTlt) j

theorem raw_intrinsic_log_euclidean_jets_bounded_on_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x : E, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ j (fun y : E => Real.log
        (axisDivision (rawWarpingRadius P G hrotation t) ‖y‖)) x‖ ≤ C := by
  let A := Icc (0 : ℝ) T
  let f (t : A) (r : ℝ) := Real.log (axisDivision (rawWarpingRadius P G hrotation t.1) r)
  have heq (t : A) : f t = intrinsicLogWarping (G.flow.metric t.1)
      (hrotation t.1 ⟨t.2.1, t.2.2.trans_lt hTlt⟩)
      (G.complete P ⟨t.2.1, t.2.2.trans_lt hTlt⟩) := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    rfl
  have hs (t : A) : ContDiff ℝ ∞ (f t) := by
    rw [heq]
    exact intrinsicLogWarping_contDiff _ _ _
  have he (t : A) : Function.Even (f t) := by
    rw [heq]
    exact intrinsicLogWarping_even _ _ _
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, |r| ≤ R →
      |iteratedDeriv j (f t) r| ≤ C := by
    have hc : Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2) :=
      raw_intrinsic_log_jet_continuous_subtype P G hrotation hT hTlt j
    obtain ⟨C, hCb⟩ :=
      (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-R) R))).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t r hr
    have hbval : |iteratedDeriv j (f t) r| ≤ C := by
      simpa only [Real.norm_eq_abs] using hCb (t, r) ⟨mem_univ _, abs_le.mp hr⟩
    exact hbval.trans (le_max_left C 0)
  intro j
  obtain ⟨C, hC, hCb⟩ := RadialGauge.even_radial_compact_jets_bounded (E := E) hR hs he hb j
  exact ⟨C, hC, fun t ht => hCb ⟨t, ht⟩⟩

end PoincareConjecture.M35.Uniqueness
