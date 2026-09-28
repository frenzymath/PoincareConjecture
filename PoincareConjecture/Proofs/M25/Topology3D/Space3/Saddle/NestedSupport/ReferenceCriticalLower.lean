import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceLowerSourceCircles
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.ReferenceCriticalValues
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

local notation "D2" =>
  Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞

set_option maxHeartbeats 1000000 in






theorem exists_reference_critical_lower_data
    (R : ℝ) (hR : 0 < R)
    (ws wm d rho deltaTar : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hrho : 0 < rho) (hdeltaTar : 0 < deltaTar)
    (_hsmallTar : deltaTar ≤ rho ^ 2 / 128) :
    let rhoN : ℝ := R / 2
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let muMax : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    let muTar : ℝ := deltaTar / rho ^ 2
    ∃ (_hrhoN : 0 < rhoN) (deltaN : ℝ) (_hdeltaN : 0 < deltaN)
      (_hsmallN : deltaN ≤ rhoN ^ 2 / 128)
      (_hgapLo : 4 * deltaN < k - 17 / 16)
      (_hgapHi : 4 * deltaN < muMax - k)
      (_hmuRef : deltaN / rhoN ^ 2 < muTar)
      (_hdeltaHalf : deltaN ≤ rhoN ^ 2 * muTar / 2)
      (B0 : Fin 2 → BallNeighborhoodChart E2 E2) (Tlower : D2)
      (q : Fin 2 → UnitCircle → UnitTwoSphere),
      (∀ i : Fin 2, (B0 i).chart.source = univ ∧
        (B0 i).chart.target = univ) ∧
      (B0 0).closedRegion ⊆ (B0 1).inside ∧
      {x : E2 | heightCoordinates.symm (x, 17 / 16 + d) ∈
        (nestedReferenceBallChart d).closedRegion} =
        (B0 1).closedRegion \ (B0 0).inside ∧
      {x : E2 | heightCoordinates.symm (x, 17 / 16 + d) ∈
        (nestedReferenceBallChart d).inside} =
        (B0 1).inside \ (B0 0).closedRegion ∧
      (∀ i : Fin 2,
        ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
        ∀ theta : UnitCircle,
          Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
      (∀ i l : Fin 2, i ≠ l →
        Disjoint (range (q i)) (range (q l))) ∧
      (⋃ i : Fin 2, range (q i)) =
        {p : UnitTwoSphere |
          (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
            k + d - deltaN} ∧
      (∀ i : Fin 2, ∀ theta : UnitCircle,
        nestedReferenceDiffeomorph d (q i theta : E3) =
          heightCoordinates.symm
            (Tlower ((B0 i).chart (theta : E2)), k + d - deltaN)) := by
  classical
  dsimp only
  let rhoN : ℝ := R / 2
  let k : ℝ :=
    1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
  let muMax : ℝ :=
    1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
  let muTar : ℝ := deltaTar / rho ^ 2
  have hrhoN : 0 < rhoN := by
    dsimp [rhoN]
    linarith
  have hHigh := NestedReferenceLower.reference_high_sphere_regularity
    ws wm d hwslo hwshi hwsroot
    hwmlo hwmhi hwmroot
  dsimp only at hHigh
  obtain ⟨_, hK37, hK54, hMu54, _, _, _, _, _, _⟩ := hHigh
  have hValues := reference_critical_values_explicit ws wm hwslo hwshi hwsroot
    hwmlo hwmhi hwmroot hK37 hK54 hMu54
  dsimp only at hValues
  obtain ⟨hkValue, hmuValue, hkLower, hkGap⟩ := hValues
  have hmuTar : 0 < muTar := by
    dsimp [muTar]
    exact div_pos hdeltaTar (sq_pos_of_pos hrho)
  let d0 : ℝ := rhoN ^ 2 / 256
  let d1 : ℝ := (k - 17 / 16) / 16
  let d2 : ℝ := (muMax - k) / 16
  let d3 : ℝ := rhoN ^ 2 * muTar / 2
  let deltaN : ℝ := min d0 (min d1 (min d2 d3))
  have hd0 : 0 < d0 := by
    dsimp [d0]
    positivity
  have hkLower' : (17 : ℝ) / 16 < k := by
    calc
      (17 : ℝ) / 16 <
          ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2 +
            Real.sqrt (1 - ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2) +
            !₂[-Real.sqrt (1 - ws ^ 2), 0] 0 / 32 := hkLower
      _ = k := hkValue
  have hkGap' : k < muMax := by
    calc
      k = ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2 +
          Real.sqrt (1 - ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2) +
          !₂[-Real.sqrt (1 - ws ^ 2), 0] 0 / 32 := hkValue.symm
      _ < ‖!₂[Real.sqrt (1 - wm ^ 2), 0]‖ ^ 2 +
          Real.sqrt (1 - ‖!₂[Real.sqrt (1 - wm ^ 2), 0]‖ ^ 2) +
          !₂[Real.sqrt (1 - wm ^ 2), 0] 0 / 32 := hkGap
      _ = muMax := hmuValue
  have hd1 : 0 < d1 := by
    dsimp [d1]
    linarith
  have hd2 : 0 < d2 := by
    dsimp [d2]
    linarith [hkGap']
  have hd3 : 0 < d3 := by
    dsimp [d3]
    positivity
  have hdeltaN : 0 < deltaN := by
    dsimp [deltaN]
    exact lt_min hd0 (lt_min hd1 (lt_min hd2 hd3))
  have hsmallN : deltaN ≤ rhoN ^ 2 / 128 := by
    have hle : deltaN ≤ d0 := by
      exact min_le_left _ _
    dsimp [d0] at hle
    nlinarith
  have hgapLo : 4 * deltaN < k - 17 / 16 := by
    have hle : deltaN ≤ d1 := by
      exact le_trans (min_le_right d0 _) (min_le_left d1 (min d2 d3))
    dsimp [d1] at hle
    nlinarith
  have hgapHi : 4 * deltaN < muMax - k := by
    have hle : deltaN ≤ d2 := by
      exact le_trans (min_le_right d0 _)
        (le_trans (min_le_right d1 _) (min_le_left d2 d3))
    dsimp [d2] at hle
    linarith only [hle, hkGap']
  have hmuRef : deltaN / rhoN ^ 2 < muTar := by
    have hle : deltaN ≤ d3 := by
      exact le_trans (min_le_right d0 _)
        (le_trans (min_le_right d1 _) (min_le_right d2 _))
    dsimp [d3] at hle
    have hdeltaHalf : deltaN ≤ rhoN ^ 2 * muTar / 2 := hle
    have hrhoN2 : 0 < rhoN ^ 2 := sq_pos_of_pos hrhoN
    have hhalf : muTar / 2 < muTar := by linarith
    have hquot : deltaN / rhoN ^ 2 ≤ muTar / 2 := by
      apply (div_le_iff₀ hrhoN2).2
      calc
        deltaN ≤ rhoN ^ 2 * muTar / 2 := hdeltaHalf
        _ = (muTar / 2) * rhoN ^ 2 := by ring
    exact lt_of_le_of_lt hquot hhalf
  have haLower : (17 : ℝ) / 16 ≤ k - deltaN := by
    nlinarith [hgapLo]
  have haUpper : k - deltaN < k := by linarith
  have hLower := NestedReferenceLower.exists_reference_lower_source_circles
    ws wm d (k - deltaN) hwslo hwshi hwsroot hwmlo hwmhi hwmroot haLower
  have haUpper' : k - deltaN <
      ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2 +
        Real.sqrt (1 - ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2) +
        !₂[-Real.sqrt (1 - ws ^ 2), 0] 0 / 32 := by
    calc
      k - deltaN < k := haUpper
      _ = ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2 +
          Real.sqrt (1 - ‖!₂[-Real.sqrt (1 - ws ^ 2), 0]‖ ^ 2) +
          !₂[-Real.sqrt (1 - ws ^ 2), 0] 0 / 32 := hkValue.symm
  have hLower' := hLower haUpper'
  dsimp only at hLower'
  obtain ⟨B0, T, _, q, hB0, hnest, hclosed, hinside, hreg, heta, hI, hTs,
    hTi, hT0, hC, hB, hTlevel, hlevels, hq, hqpair,
    hqlevel, hqreconstruct⟩ := hLower'
  let Tlower : D2 := T (k - deltaN + d)
  have hqlevel' : (⋃ i : Fin 2, range (q i)) =
      {p : UnitTwoSphere |
        (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
          k + d - deltaN} := by
    simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hqlevel
  have hqreconstruct' (i : Fin 2) (theta : UnitCircle) :
      nestedReferenceDiffeomorph d (q i theta : E3) =
        heightCoordinates.symm
          (Tlower ((B0 i).chart (theta : E2)), k + d - deltaN) := by
    change nestedReferenceDiffeomorph d (q i theta : E3) =
      heightCoordinates.symm
        (T (k - deltaN + d) ((B0 i).chart (theta : E2)), k + d - deltaN)
    simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hqreconstruct i theta
  have hdeltaHalf : deltaN ≤ rhoN ^ 2 * muTar / 2 := by
    exact le_trans (min_le_right d0 _)
      (le_trans (min_le_right d1 _) (min_le_right d2 _))
  refine ⟨hrhoN, deltaN, hdeltaN, hsmallN, hgapLo, hgapHi, hmuRef,
    hdeltaHalf,
    B0, Tlower, q, hB0, hnest, hclosed, hinside, hq, hqpair, hqlevel',
    hqreconstruct'⟩

end PoincareConjecture.M25.Topology3D
