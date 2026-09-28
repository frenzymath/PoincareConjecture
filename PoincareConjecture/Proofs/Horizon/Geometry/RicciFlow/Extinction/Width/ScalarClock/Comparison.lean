import PoincareConjecture.Proofs.Horizon.Analysis.ODE.ForwardComparison
import PoincareConjecture.Definitions.M68
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Topology

universe u

namespace PoincareConjecture

private theorem m68_profile_clock_positive
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX) (t : Set.Icc I.T₁ I.T₂) :
    0 < 1 + 4 * t.1 := by
  have hT₁ : 0 ≤ I.T₁ := I.ordered.1
  have ht : I.T₁ ≤ t.1 := t.2.1
  linarith

theorem m68_profile_equation
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX) (t : Set.Icc I.T₁ I.T₂) :
    HasDerivAt (m68Profile I) (-2 * Real.pi +
      3 * m68Profile I t.1 / (1 + 4 * t.1)) t.1 := by
  have hA : 0 < 1 + 4 * t.1 := m68_profile_clock_positive I t
  have hA1 : 0 < 1 + 4 * I.T₁ := by linarith [I.ordered.1]
  have hnum : HasDerivAt (fun x : ℝ => 1 + 4 * x) 4 t.1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id t.1).const_mul 4).add_const 1
  have hquot : HasDerivAt
      (fun x : ℝ => (1 + 4 * x) / (1 + 4 * I.T₁))
      (4 / (1 + 4 * I.T₁)) t.1 := by
    simpa using hnum.div_const (1 + 4 * I.T₁)
  have hqpow := hquot.rpow_const (p := (3 : ℝ) / 4)
    (Or.inl (ne_of_gt (div_pos hA hA1)))
  have hapow := hnum.rpow_const (p := (3 : ℝ) / 4) (Or.inl (ne_of_gt hA))
  have hfirst := hqpow.const_mul (m68Profile I I.T₁)
  have hsecond := (hapow.const_mul
      (2 * Real.pi * Real.rpow (1 + 4 * I.T₁) ((1 : ℝ) / 4)))
  have hthird := hnum.const_mul (2 * Real.pi)
  have hinit : m68Profile I I.T₁ = X.width I.start := by
    dsimp [m68Profile]
    rw [div_self (ne_of_gt hA1)]
    rw [Real.one_rpow, mul_assoc, ← Real.rpow_add hA1]
    norm_num
  dsimp [m68Profile]
  convert (hfirst.add hsecond).sub hthird using 1 <;> try rfl
  · funext x
    rw [hinit]
    dsimp [m68Profile]
  · rw [hinit]
    have hratio : 0 < (1 + 4 * t.1) / (1 + 4 * I.T₁) := div_pos hA hA1
    rw [Real.rpow_sub hratio, Real.rpow_sub hA]
    rw [Real.div_rpow hA.le hA1.le, Real.div_rpow hA.le hA1.le]
    ring_nf
    simp only [Real.rpow_one, inv_inv]
    have hAt : 1 + t.1 * 4 ≠ 0 := by nlinarith [hA]
    have hA1' : 1 + I.T₁ * 4 ≠ 0 := by nlinarith [hA1]
    field_simp [hAt, hA1'] <;> ring_nf
    have hbpow : (1 + I.T₁ * 4) ^ ((1 : ℝ) / 4) =
        Real.rpow (1 + I.T₁ * 4) ((1 : ℝ) / 4) := rfl
    rw [hbpow]
    ring

theorem m68_profile_initial
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX) :
    m68Profile I I.T₁ = X.width I.start := by
  have hA1 : 0 < 1 + 4 * I.T₁ := by linarith [I.ordered.1]
  dsimp [m68Profile]
  rw [div_self (ne_of_gt hA1)]
  rw [Real.one_rpow, mul_assoc, ← Real.rpow_add hA1]
  norm_num

theorem m68_regular_profile_bound
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X} (I : M68ProfileInput X HX)
    {a b : ℝ} (ha : I.T₁ ≤ a) (hab : a ≤ b) (hb : b ≤ I.T₂)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hclock : ∀ t : Set.Icc a b, 0 < 1 + 4 * t.1)
    (hforward : ∀ s : ℝ, s ∈ Set.Icc a b → s < b → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ∈ Set.Icc a b → s < t →
        t < s + δ →
        (f t - f s) / (t - s) ≤
          -2 * Real.pi + 3 * f s / (1 + 4 * s) + ε)
    (hinit : f a ≤ m68Profile I a) :
    ∀ t : Set.Icc a b, f t.1 ≤ m68Profile I t.1 := by
  have hprofile_cont : ContinuousOn (m68Profile I) (Set.Icc a b) := by
    intro s hs
    have hsI : s ∈ Set.Icc I.T₁ I.T₂ :=
      ⟨ha.trans hs.1, hs.2.trans hb⟩
    exact (m68_profile_equation I ⟨s, hsI⟩).continuousAt.continuousWithinAt
  let J : HorizonRegularSlabInput a b :=
    { ordered := hab
      f := f
      f_continuous := hf
      G := m68Profile I
      clock_positive := by
        intro t ht
        exact hclock ⟨t, ht⟩
      initial_comparison := hinit
      profile_continuous := hprofile_cont
      forward_difference := by
        intro s hs hslt ε hε
        exact hforward s hs hslt ε hε
      profile_equation := by
        intro t ht
        have htI : t ∈ Set.Icc I.T₁ I.T₂ :=
          ⟨ha.trans ht.1, ht.2.trans hb⟩
        exact (m68_profile_equation I ⟨t, htI⟩).hasDerivWithinAt }
  intro t
  exact (Classical.choice (horizon_regularSlabComparison a b J)).comparison t t.2

theorem m68_no_event_interval_bound
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    (HX : M67Conclusion X) (I : M68ProfileInput X HX)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ I.T₂)
    (hI : I.T₁ ≤ a) (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (hinit : X.width (M68ProfileInput.time I ⟨a, ⟨hI, hab.le.trans hb⟩⟩) ≤ m68Profile I a) :
    ∀ t : Set.Icc a b,
      X.width ⟨t.1, ha.trans t.2.1,
        t.2.2.trans (hb.trans I.ordered.2.2)⟩ ≤ m68Profile I t.1 := by
  have hbT : b ≤ T := hb.trans I.ordered.2.2
  let R := Classical.choice (X.regular_piece ha hab hbT hJ)
  let Q := R.input
  let MC := R.conclusion
  let embed : Set.Icc a b → Set.Icc (0 : ℝ) T :=
    fun s => ⟨s.1, ha.trans s.2.1, s.2.2.trans hbT⟩
  have hwidth (s : Set.Icc a b) : X.width (embed s) = m66Width Q s := by
    have h := R.width_agreement s
    have heq : R.interval s = embed s := by
      ext
      exact R.interval_time s
    simpa [embed, heq] using h
  let f : ℝ → ℝ := fun x =>
    if hx : x ∈ Set.Icc a b then m66Width Q ⟨x, hx.1, hx.2⟩ else 0
  have hcont : ContinuousOn f (Set.Icc a b) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have heq : (Set.Icc a b).domRestrict f =
        (fun s : Set.Icc a b => m66Width Q s) := by
      funext s
      dsimp [Set.domRestrict, f]
      split
      · rfl
      · rename_i hfalse
        exact (hfalse s.property).elim
    rw [heq]
    exact continuous_iff_continuousAt.mpr (fun s => MC.continuous_at s)
  have hclock : ∀ t : Set.Icc a b, 0 < 1 + 4 * t.1 := by
    intro t
    have : 0 ≤ t.1 := ha.trans t.2.1
    linarith
  have hforward : ∀ s : ℝ, s ∈ Set.Icc a b → s < b → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ∈ Set.Icc a b → s < t →
        t < s + δ →
        (f t - f s) / (t - s) ≤
        -2 * Real.pi + 3 * f s / (1 + 4 * s) + ε := by
    intro s hs hsb ε hε
    let ss : Set.Icc (0 : ℝ) T := embed ⟨s, hs.1, hs.2⟩
    obtain ⟨δ, hδ, hquot⟩ := HX.forward_difference ss
      (by dsimp [ss, embed]; exact lt_of_lt_of_le hsb hbT) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t ht hst hts
    have hquot' := hquot (embed ⟨t, ht.1, ht.2⟩) hst hts
    have hwt := hwidth ⟨t, ht.1, ht.2⟩
    have hws := hwidth ⟨s, hs.1, hs.2⟩
    have hws' : X.width ss = m66Width Q ⟨s, hs.1, hs.2⟩ := by simpa [ss] using hws
    have hnonneg := HX.width_nonnegative ss
    have hlow := X.scalar_lower_bound ss
    change -6 / (1 + 4 * s) ≤ X.scalar_infimum ss at hlow
    have hden : 0 < 1 + 4 * s := by linarith [ha.trans hs.1]
    simp only [f, dif_pos ht, dif_pos hs]
    rw [← hwt, ← hws]
    have hmul : 0 ≤ ((6 / (1 + 4 * s) + X.scalar_infimum ss) / 2) *
        m66Width Q ⟨s, hs.1, hs.2⟩ := by
      have hnonneg' : 0 ≤ 6 / (1 + 4 * s) + X.scalar_infimum ss := by
        have hid : 6 / (1 + 4 * s) = -(-6 / (1 + 4 * s)) := by ring
        rw [hid]
        linarith
      have hnonnegQ : 0 ≤ m66Width Q ⟨s, hs.1, hs.2⟩ :=
        MC.width_nonnegative ⟨s, hs.1, hs.2⟩
      exact mul_nonneg (div_nonneg hnonneg' (by norm_num)) hnonnegQ
    change (X.width (embed ⟨t, ht.1, ht.2⟩) - X.width ss) / (t - s) ≤
      -2 * Real.pi - X.scalar_infimum ss / 2 * X.width ss + ε at hquot'
    rw [hws] at hquot'
    rw [hwt] at hquot'
    have hrel : -X.scalar_infimum ss / 2 * m66Width Q ⟨s, hs.1, hs.2⟩ ≤
        3 * m66Width Q ⟨s, hs.1, hs.2⟩ / (1 + 4 * s) := by
      field_simp [ne_of_gt hden] at hmul ⊢
      nlinarith [hmul]
    rw [hws, hwt]
    linarith
  have hinit' : f a ≤ m68Profile I a := by
    dsimp [f]
    rw [dif_pos ⟨le_rfl, hab.le⟩]
    rw [← hwidth ⟨a, le_rfl, hab.le⟩]
    simpa [M68ProfileInput.time, embed] using hinit
  have hbound := m68_regular_profile_bound I hI hab.le hb f hcont hclock hforward hinit'
  intro t
  rw [hwidth t]
  simpa only [f, dif_pos t.property] using hbound t

end PoincareConjecture
