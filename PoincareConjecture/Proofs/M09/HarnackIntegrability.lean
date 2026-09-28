import PoincareConjecture.Proofs.M09.SquareScalarDerivative
import PoincareConjecture.Proofs.M09.SquareEnergyRegularity
import PoincareConjecture.Proofs.M09.FamilySquareVelocity
import PoincareConjecture.Proofs.M09.FrameForms








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def backwardScalarEvolutionAlong {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M) (t : ℝ) : ℝ :=
  -((F.connection (T - t)).laplacian (F.connection (T - t)).scalarCurvature (γ t) +
    2 * (F.connection (T - t)).ricciNormSq (γ t))

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_weightedHarnack_square {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (s : ℝ) (hs : s ∈ Set.Ioo 0 (Real.sqrt b)) :
    s ^ 2 * s * reducedHarnackDensity F T (A.gamma Z)
        (backwardScalarEvolutionAlong F T (A.gamma Z)) (s ^ 2) =
      -s * (F.connection (T - s ^ 2)).scalarCurvature (A.squareFamily Z s) -
        (s ^ 2 / 2) * deriv (fun r ↦
          (F.connection (T - r ^ 2)).scalarCurvature (A.squareFamily Z r)) s -
        deriv (regularizedCurveEnergy F T (A.squareFamily Z)) s / 8 := by
  have hsmax : s ∈ Set.Ioo 0 (Real.sqrt τmax) :=
    ⟨hs.1, hs.2.trans (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hbase := A.square_agrees Z s ⟨hs.1.le, hsmax.2⟩
  have hvel := lExponentialFamily_square_velocity_eq A Z s hsmax
  have hα := (lExponentialFamily_squareSlice_contMDiffAt A Z s
    ⟨hs.1.le, hsmax.2⟩).mdifferentiableAt (by simp)
  have hS := (squareTime_scalar_along_hasDerivAt F hM04 T τmax b hb hmax hwindow
    (A.squareFamily Z) s hs hα).deriv
  have hE := (lExponentialFamily_squareEnergy_hasDerivAt hM04 hτmax hwindow
    A Z b hb hmax s (Set.Ioo_subset_Icc_self hs)).deriv
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let q := A.gamma Z (s ^ 2)
  let B := tensorBilinear g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 q
  have hB (v w : TangentSpace (𝓡 n) q) : D.ricci q v w = B v w :=
    (tensorBilinear_apply g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 q v w).symm
  have hRic (v : TangentSpace (𝓡 n) q) :
      D.ricci q ((2 * s) • v) ((2 * s) • v) = (2 * s) ^ 2 * D.ricci q v v := by
    rw [hB, hB]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hbase] at hS hE ⊢
  rw [hvel, map_smul, smul_eq_mul] at hS hE
  rw [hRic] at hE
  rw [hS, hE]
  unfold reducedHarnackDensity backwardScalarEvolutionAlong
  dsimp only [D, q] at *
  field_simp [hs.1.ne'] <;> ring

theorem lExponentialFamily_harnack_integrable {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    IntervalIntegrable (fun t ↦ t * Real.sqrt t * reducedHarnackDensity F T (A.gamma Z)
      (backwardScalarEvolutionAlong F T (A.gamma Z)) t) MeasureTheory.volume 0 b := by
  let U := ((fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain) ∩
    Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hU : IsOpen U := (A.square_open.preimage
    (continuous_const.prodMk continuous_id)).inter isOpen_Ioo
  have hKU : Set.Icc 0 (Real.sqrt b) ⊆ U := by
    intro s hs
    have hsmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact ⟨A.square_contains ⟨Set.mem_univ _, hs.1, hsmax⟩,
      (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1, hsmax⟩
  have hα := (lExponentialFamily_squareSlice_contMDiffOn A Z).mono
    (show U ⊆ (fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain from Set.inter_subset_left)
  let S : ℝ → ℝ := fun s ↦ (F.connection (T - s ^ 2)).scalarCurvature (A.squareFamily Z s)
  let E := regularizedCurveEnergy F T (A.squareFamily Z)
  have hS : ContDiffOn ℝ ∞ S U :=
    ((squareTime_scalar_smooth F hM04 T τmax hτmax hwindow).comp
      (contMDiffOn_id.prodMk hα) (fun s hs ↦ ⟨hs.2, Set.mem_univ _⟩)).contDiffOn
  have hE : ContDiffOn ℝ ∞ E U := regularizedCurveEnergy_contDiffOn F T τmax hτmax hwindow
    (A.squareFamily Z) U hU hα Set.inter_subset_right
  let H : ℝ → ℝ := fun s ↦ -s * S s - (s ^ 2 / 2) * deriv S s - deriv E s / 8
  have hH : ContinuousOn H U :=
    ((continuousOn_id.neg.mul hS.continuousOn).sub
      (((continuousOn_id.pow 2).div_const 2).mul
        (hS.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn)).sub
          ((hE.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn.div_const 8)
  have hcomp : ContinuousOn (fun t ↦ H (Real.sqrt t)) (Set.Icc 0 b) :=
    (hH.mono hKU).comp Real.continuous_sqrt.continuousOn
      (fun t ht ↦ ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩)
  apply (hcomp.intervalIntegrable_of_Icc hb.le).congr_uIoo
  intro t ht
  have ht' : t ∈ Set.Ioo 0 b := by simpa only [Set.uIoo_of_le hb.le] using ht
  have h := lExponentialFamily_weightedHarnack_square hM04 hτmax hwindow A Z b hb hmax
    (Real.sqrt t) ⟨Real.sqrt_pos.mpr ht'.1, Real.sqrt_lt_sqrt ht'.1.le ht'.2⟩
  simpa only [H, S, E, Real.sq_sqrt ht'.1.le] using h.symm

end PoincareConjecture.Proofs.M09
