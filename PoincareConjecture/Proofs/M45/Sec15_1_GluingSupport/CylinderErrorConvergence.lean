import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_VanishingOperations
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_EvolvingComponents
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M45

open M36 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem centeredCylinderMetric_contDiffAt_of_smooth {eta : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn eta B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-eta⁻¹) eta⁻¹) :
    ContDiffAt ℝ ∞ (centeredCylinderMetric B z.1 z.2) 0 := by
  apply centeredCylinderBilinear_contDiffAt
  intro i j
  have hzero : (0 : E₂) ∈ (chartAt E₂ z.1).target := by
    rw [← sphere_chart_center_zero z.1]
    exact (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  exact (hB z.1 i j).contDiffAt
    (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds ⟨hzero, hz⟩)

theorem pointJetsVanish_correctedCylinderComponent {ι : Type*} {l : Filter ι}
    {t eta : ι → ℝ} {z : ι → RoundCylinderSpace} {B : ι → RoundCylinderTwoTensor}
    (hB : ∀ i, RoundCylinderTensorSmoothOn (eta i) (B i))
    (hz : ∀ i, (z i).2 ∈ Ioo (-(eta i)⁻¹) (eta i)⁻¹)
    (h : PointJetsVanish (fun i p => centeredCylinderMetric (B i) (z i).1 (z i).2 p -
      evolvingCylinderModelField (t i) p) (fun _ => 0) l)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    PointJetsVanish (fun i => centeredCylinderComponent (staticCylinderCorrection (t i) (B i))
      (z i).1 (z i).2 k a) (fun _ => 0) l := by
  classical
  have hs (i : ι) (j : ℕ) (b : Fin (2 + j) → Fin 3) :=
    correctedCylinderComponent_contDiffAt (t := t i) (hB i) (z i) (hz i) j b
  induction k with
  | zero =>
      let e := EuclideanSpace.basisFun (Fin 3) ℝ
      let L := (ContinuousLinearMap.apply ℝ ℝ (e (a 1))).comp
        (ContinuousLinearMap.apply ℝ (E₃ →L[ℝ] ℝ) (e (a 0)))
      have hEs (i : ι) :=
        (centeredCylinderMetric_contDiffAt_of_smooth (hB i) (z i) (hz i)).sub
          (evolvingCylinderModelField_contDiff (t i)).contDiffAt
      apply (h.clm hEs L).congr
      intro i
      filter_upwards [] with p
      change (centeredCylinderMetric (B i) (z i).1 (z i).2 p -
        evolvingCylinderModelField (t i) p) (e (a 0)) (e (a 1)) = _
      have he := Eq.trans
        (staticCylinderCorrection_centered_error (t i) (B i) (z i).1 (z i).2).symm
        (centeredCylinderMetric_sub_model _ _ _)
      rw [show centeredCylinderMetric (B i) (z i).1 (z i).2 p -
          evolvingCylinderModelField (t i) p =
          centeredCylinderError (staticCylinderCorrection (t i) (B i)) (z i).1 (z i).2 p
        from congrFun he p]
      exact centeredCylinderBilinear_basis _ _ _ _ _
  | succ k ih =>
      let b : Fin (2 + k) → Fin 3 := fun j => a j.succ
      let c := fun i => centeredCylinderComponent (staticCylinderCorrection (t i) (B i))
        (z i).1 (z i).2 k
      have hd := (ih b).fderiv.clm
        (fun i => (hs i k b).fderiv_right (m := ∞) (by simp))
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)))
      have hp (j : Fin (2 + k)) (v : Fin 3) :
          PointJetsVanish (fun i p => centeredCylinderChristoffel v (a 0) (a j.succ) p *
            c i (Function.update b j v) p) (fun _ => 0) l := by
        have hfixed (m : ℕ) : FinitePointJetBounded m
            (fun _ : ι => centeredCylinderChristoffel v (a 0) (a j.succ))
            (fun _ => 0) l := by
          intro q _
          refine ⟨‖iteratedFDeriv ℝ q
            (centeredCylinderChristoffel v (a 0) (a j.succ)) (0 : E₃)‖, ?_⟩
          change ∀ᶠ _i : ι in l, ‖iteratedFDeriv ℝ q
            (centeredCylinderChristoffel v (a 0) (a j.succ)) (0 : E₃)‖ ≤ _
          exact Filter.Eventually.of_forall (fun _ => le_rfl)
        have hv := (ih (Function.update b j v)).bilinear hfixed
          (fun i => hs i k (Function.update b j v))
          (fun _ => (centeredCylinderChristoffel_contDiff v (a 0) (a j.succ)).contDiffAt)
          (ContinuousLinearMap.mul ℝ ℝ)
        simpa only [ContinuousLinearMap.mul_apply', mul_comm, c] using hv
      have hps (i : ι) (j : Fin (2 + k)) (v : Fin 3) : ContDiffAt ℝ ∞
          (fun p => centeredCylinderChristoffel v (a 0) (a j.succ) p *
            c i (Function.update b j v) p) 0 :=
        (centeredCylinderChristoffel_contDiff v (a 0) (a j.succ)).contDiffAt.mul
          (hs i k (Function.update b j v))
      have hsum := PointJetsVanish.sum Finset.univ
        (fun j _ => PointJetsVanish.sum Finset.univ (fun v _ => hp j v)
          (fun v _ i => hps i j v))
        (fun j _ i => ContDiffAt.sum (fun v _ => hps i j v))
      have hout := hd.sub hsum
        (fun i => ((hs i k b).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
        (fun i => ContDiffAt.sum (fun j _ => ContDiffAt.sum (fun v _ => hps i j v)))
      apply hout.congr
      intro i
      filter_upwards [] with p
      exact (centeredCylinderComponent_succ _ _ _ k a p).symm

theorem evolvingCylinderInverseWeight_upper {t : ℝ} (ht : t ≤ 0) (i : Fin 3) :
    evolvingCylinderInverseWeight t i ≤ 1 := by
  have hp : 0 < 2 * (1 - t) := by linarith
  have hb : (2 * (1 - t))⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by linarith)
  fin_cases i
  · exact hb
  · exact hb
  · norm_num [evolvingCylinderInverseWeight]

theorem tendsto_roundCylinderJetErrorSquared_zero {ι : Type*} {l : Filter ι}
    {t eta : ι → ℝ} {z : ι → RoundCylinderSpace} {B : ι → RoundCylinderTwoTensor}
    (ht : ∀ i, t i ∈ Icc (-1 : ℝ) 0)
    (hB : ∀ i, RoundCylinderTensorSmoothOn (eta i) (B i))
    (hz : ∀ i, (z i).2 ∈ Ioo (-(eta i)⁻¹) (eta i)⁻¹)
    (h : PointJetsVanish (fun i p => centeredCylinderMetric (B i) (z i).1 (z i).2 p -
      evolvingCylinderModelField (t i) p) (fun _ => 0) l) (N : ℕ) :
    Tendsto (fun i => roundCylinderJetErrorSquared (t i) (B i) N (z i)) l (𝓝 0) := by
  classical
  let c := fun i k => centeredCylinderComponent (staticCylinderCorrection (t i) (B i))
    (z i).1 (z i).2 k
  have hc (k : ℕ) (a : Fin (2 + k) → Fin 3) : Tendsto (fun i => c i k a 0) l (𝓝 0) :=
    (pointJetsVanish_correctedCylinderComponent hB hz h k a).values
  have he (i : ι) (k : ℕ) (a : Fin (2 + k) → Fin 3) :
      roundCylinderIteratedDerivative (t i) (chartAt E₂ (z i).1) (B i) k
        (chartAt E₂ (z i).1 (z i).1, (z i).2) a = c i k a 0 := by
    simp only [c, centeredCylinderComponent,
      staticCylinderCorrection_iteratedDerivative ((ht i).2.trans_lt (by norm_num)),
      map_zero, zero_add, sphere_chart_center_zero]
  have hn (k : ℕ) : Tendsto (fun i => roundCylinderTensorNormSquared (t i)
      (chartAt E₂ (z i).1) (chartAt E₂ (z i).1 (z i).1, (z i).2)
      (roundCylinderIteratedDerivative (t i) (chartAt E₂ (z i).1) (B i) k
        (chartAt E₂ (z i).1 (z i).1, (z i).2))) l (𝓝 0) := by
    have hs : Tendsto (fun i => ∑ a : Fin (2 + k) → Fin 3, (c i k a 0) ^ 2) l (𝓝 0) := by
      simpa only [zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero] using
        tendsto_finsetSum (s := Finset.univ) (fun a _ => (hc k a).pow 2)
    apply squeeze_zero (fun i => evolvingTensorNormSquared_nonneg
      ((ht i).2.trans_lt (by norm_num)) (z i).1 (z i).2 _) ?_ hs
    intro i
    rw [evolving_roundCylinderTensorNormSquared_center ((ht i).2.trans_lt (by norm_num))]
    apply Finset.sum_le_sum
    intro a _
    rw [he]
    apply mul_le_of_le_one_left (sq_nonneg _)
    apply Finset.prod_le_one
    · intro j _
      linarith [evolvingCylinderInverseWeight_lower (ht i) (a j)]
    · intro j _
      exact evolvingCylinderInverseWeight_upper (ht i).2 (a j)
  simpa only [roundCylinderJetErrorSquared, Finset.sum_const_zero] using
    tendsto_finsetSum (s := Finset.range (N + 1)) (fun k _ => hn k)

end PoincareConjecture.M45
