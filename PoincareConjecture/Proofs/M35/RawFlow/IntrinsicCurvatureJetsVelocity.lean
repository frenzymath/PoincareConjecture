import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTip











set_option autoImplicit false

open Set MeasureTheory
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



theorem raw_intrinsic_acceleration_jet_continuous_subtype (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ => iteratedDeriv j
      (fun r => 2 * axisDivision (deriv (deriv (rawWarpingRadius P G hrotation p.1.1))) r /
        axisDivision (rawWarpingRadius P G hrotation p.1.1) r) p.2) := by
  let A := Icc (0 : ℝ) T
  let f (t : A) := rawWarpingRadius P G hrotation t.1
  let q (t : A) := axisDivision (f t)
  let v (t : A) := axisDivision (deriv (deriv (f t)))
  have hf (t : A) : ContDiff ℝ ∞ (f t) := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hq (t : A) : ContDiff ℝ ∞ (q t) := axisDivision_contDiff (hf t)
  have hdd (t : A) : ContDiff ℝ ∞ (deriv (deriv (f t))) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp (hf t)).2).2
  have hv (t : A) : ContDiff ℝ ∞ (v t) := axisDivision_contDiff (hdd t)
  have hqn (t : A) (r : ℝ) : q t r ≠ 0 := by
    dsimp only [q, f]
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact (intrinsicWarpingQuotient_pos _ _ _ r).ne'
  have hqc (i : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv i (q p.1) p.2) :=
    raw_intrinsic_quotient_jet_continuous_subtype P G hrotation hT hTlt i
  have hvc (i : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv i (v p.1) p.2) := by
    apply RadialGauge.axisDivision_jet_continuous hdd i
    simpa only [iteratedDeriv_succ', Nat.add_assoc] using
      raw_intrinsic_jet_continuous_subtype P G hrotation hT hTlt (i + 3)
  have hqi := RadialGauge.scalar_jets_continuous_inv hq hqn hqc
  have hm := RadialGauge.scalar_jet_continuous_mul j hv
    (fun t => (hq t).inv (hqn t)) (fun i _ => hvc i) (fun i _ => hqi i)
  have hmul := continuous_mul.comp ((continuous_const (y := (2 : ℝ))).prodMk hm)
  simpa only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_assoc,
    iteratedDeriv_const_mul_field, q, v, f] using hmul



theorem raw_intrinsic_velocity_jet_continuous_subtype (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (rawRadialVelocity P G hrotation p.1.1) p.2) := by
  let A := Icc (0 : ℝ) T
  let a (t : A) (r : ℝ) :=
    2 * axisDivision (deriv (deriv (rawWarpingRadius P G hrotation t.1))) r /
      axisDivision (rawWarpingRadius P G hrotation t.1) r
  have hac (i : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv i (a p.1) p.2) :=
    raw_intrinsic_acceleration_jet_continuous_subtype P G hrotation hT hTlt i
  have hae (t : A) : a t = intrinsicRadialAcceleration (G.flow.metric t.1)
      (hrotation t.1 ⟨t.2.1, t.2.2.trans_lt hTlt⟩)
      (G.complete P ⟨t.2.1, t.2.2.trans_lt hTlt⟩) := by
    dsimp only [a]
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    rfl
  have hd (t : A) : deriv (rawRadialVelocity P G hrotation t.1) = a t := by
    rw [rawRadialVelocity_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩, hae]
    exact funext (fun r => (intrinsicRadialVelocity_hasDerivAt _ _ _ r).deriv)
  cases j with
  | zero =>
      have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : A × ℝ) s => a p.1 s)
        ((hac 0).comp (continuous_fst.fst.prodMk continuous_snd))
        (a₀ := (0 : ℝ)) (μ := volume) (s := fun p : A × ℝ => p.2) continuous_snd
      apply hint.congr
      intro p
      simp only [iteratedDeriv_zero, rawRadialVelocity_eq P G hrotation
        ⟨p.1.2.1, p.1.2.2.trans_lt hTlt⟩, intrinsicRadialVelocity, hae]
  | succ n => simpa only [iteratedDeriv_succ', hd] using hac n



theorem raw_intrinsic_xi_jet_continuous_subtype (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (axisDivision (rawRadialVelocity P G hrotation p.1.1)) p.2) := by
  apply RadialGauge.axisDivision_jet_continuous
    (f := fun t : Icc (0 : ℝ) T => rawRadialVelocity P G hrotation t.1) (j := j)
  · intro t
    rw [rawRadialVelocity_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact intrinsicRadialVelocity_contDiff _ _ _
  · exact raw_intrinsic_velocity_jet_continuous_subtype P G hrotation hT hTlt (j + 1)

end PoincareConjecture.M35.Uniqueness
