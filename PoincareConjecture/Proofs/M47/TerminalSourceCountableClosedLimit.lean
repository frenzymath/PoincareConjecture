import PoincareConjecture.Proofs.M47.TerminalSourceCountableClosedBounds
import PoincareConjecture.Proofs.M47.TerminalGermsClosedCoefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSourceCountable_closed_limit {tau : ℝ} (htau : 0 < tau)
    {U : Set E} (hU : IsOpen U) (f : ℕ → ℝ × E → V)
    (B0 : E → V) (Bminus : ℝ × E → V)
    (hB0 : ContDiffOn ℝ ∞ B0 U)
    (hminus : ContDiffOn ℝ ∞ Bminus (Ioo (-(tau / 2)) 0 ×ˢ U))
    (hzero : ∀ x ∈ U, Tendsto (fun k => f k (0, x)) atTop (𝓝 (B0 x)))
    (hjets : ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 2)) 0 ×ˢ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
        (iteratedFDeriv ℝ m Bminus) atTop K)
    (hbound : ∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in atTop,
      ∀ z ∈ Ioo (-(tau / 2)) 0 ×ˢ U, ‖iteratedFDeriv ℝ m (f k) z‖ ≤ D)
    (htime : ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Ioo (-(tau / 2)) 0, ∀ x ∈ U,
        ‖f k (t, x) - f k (0, x)‖ ≤ D * |t|) :
    let G := fun z : ℝ × E => if z.1 < 0 then Bminus z else B0 z.2
    ContDiffOn ℝ ∞ G (Icc (-(tau / 4)) 0 ×ˢ U) ∧
      (∀ t ∈ Icc (-(tau / 4)) 0, ∀ x ∈ U,
        Tendsto (fun k => f k (t, x)) atTop (𝓝 (G (t, x)))) ∧
      ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 4)) 0 ×ˢ U →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
          (iteratedFDeriv ℝ m G) atTop K := by
  let G := fun z : ℝ × E => if z.1 < 0 then Bminus z else B0 z.2
  have hpoint (m : ℕ) (z : ℝ × E) (hz : z ∈ Ioo (-(tau / 2)) 0 ×ˢ U) :=
    (hjets m {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
      (mem_singleton z)
  have hvalue (t : ℝ) (ht : t ∈ Ioo (-(tau / 2)) 0) (x : E) (hx : x ∈ U) :
      Tendsto (fun k => f k (t, x)) atTop (𝓝 (Bminus (t, x))) := by
    have h := ((ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × E)).continuous.tendsto _).comp (hpoint 0 (t, x) ⟨ht, hx⟩)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h
  obtain ⟨D, _hD, htime⟩ := htime
  have hendpoint := terminalGerms_uniform_endpoint_bound f B0 Bminus hzero hvalue
    (fun t ht x hx => htime.mono fun k hk => hk t ht x hx)
  have hgerm {z : ℝ × E} (hz : z.1 < 0) : G =ᶠ[𝓝 z] Bminus := by
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
    exact if_pos hy
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz.2)
    have hbuffer : closedBall z.2 (r / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
    have hlocal := terminalGerms_closed_coefficient_gluing hU
      (by linarith : -(tau / 2) < -(tau / 4)) (by linarith : -(tau / 4) < 0)
      z.2 (half_pos hr) hbuffer B0 Bminus hB0.continuousOn hminus hendpoint f
      (fun m q hq => hpoint (m + 1) q
        ⟨⟨by linarith [hq.1.1], hq.1.2⟩, hbuffer (ball_subset_closedBall hq.2)⟩) ?_
    · apply (hlocal z ⟨hz.1, mem_closedBall_self (half_pos hr).le⟩).mono_of_mem_nhdsWithin
      rw [nhdsWithin_prod_eq]
      exact Filter.prod_mem_prod self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds z.2 (half_pos hr)))
    · intro m
      obtain ⟨K, hK, hbound⟩ := hbound (m + 1)
      refine ⟨⟨K, hK⟩, hbound.mono ?_⟩
      intro k hk q hq
      exact hk q ⟨⟨by linarith [hq.1.1], hq.1.2⟩,
        hbuffer (ball_subset_closedBall hq.2)⟩
  · intro t ht x hx
    by_cases ht0 : t < 0
    · simpa only [G, if_pos ht0] using hvalue t ⟨by linarith [ht.1], ht0⟩ x hx
    · have htzero : t = 0 := le_antisymm ht.2 (le_of_not_gt ht0)
      subst t
      simpa only [G, lt_self_iff_false, if_false] using hzero x hx
  · intro m K hK hKU
    apply (hjets m K hK (fun z hz =>
      ⟨⟨by linarith [(hKU hz).1.1], (hKU hz).1.2⟩, (hKU hz).2⟩)).congr_right
    intro z hz
    exact ((hgerm (hKU hz).1.2).iteratedFDeriv ℝ m).eq_of_nhds.symm



theorem terminalSourceCountable_g4_closed_limit (j : ℕ)
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {tau R L eta rho : ℝ} (htau : 0 < tau) (hrho : 0 < rho)
    (hrhoR : 2 * rho < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * rho →
      ((13 * max (4 * L / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L / 3) 1) * s ^ 2)) ≤ 3)
    (F0 : {k : ℕ // j ≤ k} → SurgeryFlowData.{u})
    (O : ∀ a, SurgeryObservation (F0 a))
    (W : ∀ a, M33RegularHistoryWindow (F0 a))
    (H : ∀ a, M33RegularHistoryData (W a))
    (C0 : {k : ℕ // j ≤ k} → GeneralizedSliceCarrier.{u})
    (base Q rNext : {k : ℕ // j ≤ k} → ℝ)
    (U : ∀ a, Opens (C0 a).carrier)
    (e : ∀ a, GeneralizedFlowCylinder (H a).generalized (C0 a)
      (base a) (Q a) (Icc (-tau) 0) (U a : Set (C0 a).carrier))
    (F : ∀ a, RicciFlow 3 (U a) (Icc (-tau) 0))
    (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)
    (hGood : ∀ᶠ a in Filter.comap
        (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
      TerminalSourceJetsG4Good S B p (O a) (H a) (U a) (e a) (F a)
        (τ := tau) (base := base a) (Q := Q a) (rNext := rNext a)
        (R := R) (L := L) (eta := eta) (C a))
    (f0 : ℕ → E → V)
    (hread : ∀ a, EqOn (f0 a.val)
      (((F a).metric 0).pullbackCoefficients (C a).chart) (ball 0 (rho / 2)))
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (B0 : E → V) (Bminus : ℝ × E → V)
    (hB0 : ContDiffOn ℝ ∞ B0 (ball 0 (rho / 2)))
    (hminus : ContDiffOn ℝ ∞ Bminus (Ioo (-(tau / 2)) 0 ×ˢ ball 0 (rho / 2)))
    (hzero : ∀ x ∈ ball 0 (rho / 2),
      Tendsto (fun k => f0 (sigma k) x) atTop (𝓝 (B0 x)))
    (hjets : ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 2)) 0 ×ˢ ball 0 (rho / 2) →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
        (terminalSourceCountableNegative j (fun a => (U a : Type u)) F C f0 (sigma k)))
        (iteratedFDeriv ℝ m Bminus) atTop K) :
    let f := terminalSourceCountableNegative j (fun a => (U a : Type u)) F C f0
    let G := fun z : ℝ × E => if z.1 < 0 then Bminus z else B0 z.2
    ContDiffOn ℝ ∞ G (Icc (-(tau / 4)) 0 ×ˢ ball 0 (rho / 2)) ∧
      (∀ t ∈ Icc (-(tau / 4)) 0, ∀ x ∈ ball 0 (rho / 2),
        Tendsto (fun k => f (sigma k) (t, x)) atTop (𝓝 (G (t, x)))) ∧
      ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 4)) 0 ×ˢ ball 0 (rho / 2) →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f (sigma k)))
          (iteratedFDeriv ℝ m G) atTop K := by
  let f := terminalSourceCountableNegative j (fun a => (U a : Type u)) F C f0
  have hz := terminalSourceCountableNegative_zero j (fun a => (U a : Type u))
    F C (terminalSourceCountableDomain rho) f0 hread
  have hbound := (terminalSourceCountable_g4_jet_bounds j S B p P htau hrho hrhoR
    hsmall F0 O W H C0 base Q rNext U e F C hGood f0 hread).2
  obtain ⟨D, hD, htime⟩ := (terminalSourceCountable_g4_closed_bounds j S B p P
    htau hrho hrhoR hsmall F0 O W H C0 base Q rNext U e F C hGood f0 hread).2
  apply terminalSourceCountable_closed_limit htau isOpen_ball
    (fun k => f (sigma k)) B0 Bminus hB0 hminus ?_ hjets ?_ ?_
  · intro x hx
    have heq : (fun k => f (sigma k) (0, x)) = (fun k => f0 (sigma k) x) :=
      funext fun k => hz (sigma k) hx
    rw [heq]
    exact hzero x hx
  · intro m
    obtain ⟨K, hK, hbound⟩ := hbound m
    refine ⟨K, hK, (hsigma.tendsto_atTop.eventually hbound).mono ?_⟩
    intro k hk z hz
    exact hk z.1 hz.1 z.2 (ball_subset_closedBall (ball_subset_ball (by linarith) hz.2))
  · refine ⟨D, hD, (hsigma.tendsto_atTop.eventually htime).mono ?_⟩
    intro k hk t ht x hx
    have heq : f (sigma k) (0, x) = f0 (sigma k) x := hz (sigma k) hx
    rw [heq]
    exact hk t ht x hx

end PoincareConjecture.M47
