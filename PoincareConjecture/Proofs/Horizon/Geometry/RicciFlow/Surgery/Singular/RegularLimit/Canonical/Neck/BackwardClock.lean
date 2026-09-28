import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ScalarMonotonicity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

theorem backward_clock_start_lt {t T R S : ℝ}
    (ht : t < T) (hR : 0 < R) (hRS : R < S) :
    t - R⁻¹ < T - S⁻¹ := by
  have hinv : S⁻¹ < R⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hR hRS
  linarith

theorem backward_clock_cover {t T R S : ℝ}
    (ht : t < T) (hR : 0 < R) (hRS : R < S) :
    Ioc (T - S⁻¹) T ⊆ Ioc (t - R⁻¹) t ∪ Ioc t T := by
  intro z hz
  by_cases hzt : z ≤ t
  · exact Or.inl ⟨(backward_clock_start_lt ht hR hRS).trans hz.1, hzt⟩
  · exact Or.inr ⟨lt_of_not_ge hzt, hz.2⟩

theorem backward_clock_reparametrize {t T R S : ℝ}
    (ht : t < T) (hR : 0 < R) (hRS : R < S)
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0) :
    T + s / S ∈ Ioc (T - S⁻¹) T ∧
      (T + s / S ≤ t → (T + s / S - t) * R ∈ Ioc (-1 : ℝ) 0) ∧
      t + ((T + s / S - t) * R) / R = T + s / S := by
  have hS : 0 < S := hR.trans hRS
  have hclock : T + s / S ∈ Ioc (T - S⁻¹) T := by
    refine ⟨?_, ?_⟩
    · have h := div_lt_div_of_pos_right hs.1 hS
      simp only [neg_div, one_div] at h
      linarith
    · have h := div_nonpos_of_nonpos_of_nonneg hs.2 hS.le
      linarith
  refine ⟨hclock, ?_, ?_⟩
  · intro htime
    have hstart := (backward_clock_start_lt ht hR hRS).trans hclock.1
    have hlow : -1 / R < T + s / S - t := by
      simp only [neg_div, one_div]
      linarith
    exact ⟨(div_lt_iff₀ hR).mp hlow,
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htime) hR.le⟩
  · rw [mul_div_cancel_right₀ _ hR.ne']
    ring

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.GeneralizedStrongNeck

theorem inverse_scale_sq_eq_scalar {F : GeneralizedRicciFlowData.{u}}
    {t ε : ℝ} (N : GeneralizedStrongNeck F t ε) :
    N.scale⁻¹ ^ 2 = (F.connection t).scalarCurvature N.center := by
  have hscale : N.scale = (Real.sqrt ((F.connection t).scalarCurvature N.center))⁻¹ := by
    rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le,
      Real.sqrt_eq_rpow]
  rw [hscale, inv_inv, Real.sq_sqrt N.scalar_center_pos.le]

end PoincareConjecture.GeneralizedStrongNeck

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem neck_backward_clock_of_strictMonoOn (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : H.regularRegion P04)
    {a : ℝ} (ha : H.reference.tMinus < a)
    (hmono : StrictMonoOn
      (fun s => ((H.terminalFlow P04).connection s).scalarCurvature x) (Ioc a T))
    {t : ℝ} (ht : t ∈ Ioo a T) (N : GeneralizedStrongNeck F t H.epsilon)
    (hcenter : N.center = H.reference.forward t ⟨(ha.trans ht.1).le, ht.2⟩ x)
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0) :
    let S := (H.terminalConnection P04).scalarCurvature x
    T + s / S ∈ Ioc (T - S⁻¹) T ∧
      (T + s / S ≤ t →
        (T + s / S - t) * (N.scale⁻¹ ^ 2) ∈ Ioc (-1 : ℝ) 0) ∧
      t + ((T + s / S - t) * (N.scale⁻¹ ^ 2)) / (N.scale⁻¹ ^ 2) = T + s / S := by
  dsimp only
  have hR : (F.connection t).scalarCurvature N.center =
      ((H.terminalFlow P04).connection t).scalarCurvature x := by
    rw [H.terminalFlow_scalar_of_ne P04 ht.2.ne, hcenter]
    exact H.reference.scalar_pullback t ⟨(ha.trans ht.1).le, ht.2⟩ x
  have hRS : (F.connection t).scalarCurvature N.center <
      (H.terminalConnection P04).scalarCurvature x := by
    rw [hR, ← H.terminalFlow_scalar_at_terminal P04 x]
    exact hmono ⟨ht.1, ht.2.le⟩ ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
  rw [N.inverse_scale_sq_eq_scalar]
  exact SingularRegularLimit.backward_clock_reparametrize ht.2 N.scalar_center_pos hRS hs

end PoincareConjecture.SingularTimeAssumptions
