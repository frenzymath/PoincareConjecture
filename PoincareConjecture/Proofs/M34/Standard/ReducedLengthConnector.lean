import PoincareConjecture.Proofs.M34.Standard.ConnectorActionBound
import PoincareConjecture.Proofs.M09.FamilyEndpointEquation
import PoincareConjecture.Statements.Ch06.ReducedVolume











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M34

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]




theorem reducedLength_le_of_smooth_connector {J : Set ℝ} (F : RicciFlow n M J)
    (P : RicciFlowCurvatureTheory.{u}) (T taumax : ℝ) (hmax : 0 < taumax)
    (hwindow : Icc (T - taumax) T ⊆ J) (L : LGeodesicTheory F T taumax)
    {tau1 tau0 B : ℝ} (htau1 : 0 < tau1) (htaus : tau1 < tau0)
    (htau0 : tau0 < taumax) (p q y : M)
    (A : LExponentialGeometry F T taumax p)
    (hq : reducedLength F T p q tau1 ≤ (n : ℝ) / 2)
    (beta : ℝ → M) (hbeta : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ beta)
    (hstart : beta (Real.sqrt tau1) = q) (hend : beta (Real.sqrt tau0) = y)
    (haction : (∫ s in Real.sqrt tau1..Real.sqrt tau0,
      squareCurveActionDensity F T beta s) ≤ B) :
    reducedLength F T p y tau0 ≤ ((n : ℝ) * Real.sqrt tau1 + B) /
      (2 * Real.sqrt tau0) := by
  have htau0pos := htau1.trans htaus
  have htau1max := htaus.trans htau0
  obtain ⟨Q, hQ0, hQ1, hQmin, hQvalue⟩ :=
    L.reduced_length_attained tau1 htau1 htau1max.le p q
  obtain ⟨Z, hZ, _⟩ := A.minimizers_lift tau1 htau1 htau1max Q hQ0 hQmin
  let alpha := A.squareFamily Z
  let D := (fun s : ℝ => (Z, s)) ⁻¹' A.squareDomain
  have hD : IsOpen D := A.square_open.preimage (continuous_const.prodMk continuous_id)
  have hID : Icc 0 (Real.sqrt tau0) ⊆ D := by
    intro s hs
    exact A.square_contains ⟨mem_univ _, hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt htau0pos.le htau0)⟩
  have halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha D :=
    lExponentialFamily_squareSlice_contMDiffOn A.toLExponentialFamily Z
  have hprefix : (∫ s in 0..Real.sqrt tau1,
      squareCurveActionDensity F T alpha s) = backwardLLength F T 0 tau1 Q.curve := by
    rw [← backwardLLength_smoothSquare_eq_integral F T tau1 htau1 alpha D hD
      ((Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt htaus.le)).trans hID) halpha]
    rw [lExponentialFamily_action_comp_sqrt_eq_of_eqOn A.toLExponentialFamily Z
      tau1 htau1 htau1max alpha (fun _ _ => rfl)]
    apply backwardLLength_congr_Ioo F T 0 tau1 htau1.le
    intro s hs
    exact (hZ (Ioo_subset_Icc_self hs)).symm
  have hprefixBound : backwardLLength F T 0 tau1 Q.curve ≤
      (n : ℝ) * Real.sqrt tau1 := by
    rw [hQvalue] at hq
    have h := (div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr htau1))).mp hq
    nlinarith
  have hjoin : alpha (Real.sqrt tau1) = beta (Real.sqrt tau1) := by
    rw [hstart]
    have hsq := A.square_agrees Z (Real.sqrt tau1)
      ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt htau1.le htau1max⟩
    have hz1 := hZ (show tau1 ∈ Icc 0 tau1 from ⟨htau1.le, le_rfl⟩)
    simpa only [Real.sq_sqrt htau1.le, ← hz1, hQ1] using hsq
  obtain ⟨Q0, hQ00, hQ0t, hQ0min, hQ0value⟩ :=
    L.reduced_length_attained tau0 htau0pos htau0.le p y
  have hcomp := minimizing_action_le_broken_square_action F P T taumax hmax hwindow
    tau0 htau0pos htau0 Q0 hQ0min alpha beta D hD hID halpha hbeta.contMDiffOn
    (Real.sqrt tau1) ⟨Real.sqrt_pos.mpr htau1, Real.sqrt_lt_sqrt htau1.le htaus⟩
    hjoin ((A.square_at_zero Z).trans hQ00.symm) (hend.trans hQ0t.symm)
  rw [hprefix] at hcomp
  rw [hQ0value]
  exact div_le_div_of_nonneg_right (hcomp.trans (add_le_add hprefixBound haction))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

end PoincareConjecture.M34
