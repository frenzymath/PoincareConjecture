import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureAmbientDerivative
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurveTimeRegularity










set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem m63FirstJet_time_self_pair [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let R := D.riemannEvaluation
    let T := D.covariantTensorDerivative D.ricciEvaluation
    let U := D.covariantTensorDerivative T
    let J := D.covariantTensorDerivative R
    let S := spatialUnitTangent F c t x
    let H := m63CurvatureJet F c 0 t x
    let B := m63CurvatureJet F c 1 t x
    let A := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
    let E := J (c x t) ![S, H, S, B, S] + R (c x t) ![B, S, B, S] +
      2 * R (c x t) ![H, S, B, H] - 2 * U (c x t) ![S, S, S, B] +
      U (c x t) ![S, B, S, S] - 3 * T (c x t) ![H, S, B] -
      3 * T (c x t) ![S, H, B] + 3 * T (c x t) ![B, S, H]
    (F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative D (fun s => c x s)
          (fun s => m63CurvatureJet F c 1 s x) t) B =
      (F.metric t).inner (c x t) (m63CurvatureJet F c 3 t x) B +
        3 * A x * m63CurvatureJetSquared F c 1 t x +
        3 * m62ArcDerivative F c t A x * (F.metric t).inner (c x t) H B +
        m62ArcSecondDerivative F c t A x * (F.metric t).inner (c x t) S B + E := by
  let D := F.connection t
  let R := D.riemannEvaluation
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let J := D.covariantTensorDerivative R
  let S : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => spatialUnitTangent F c z.2 z.1
  let H : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c 0 z.2 z.1
  let B : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c 1 z.2 z.1
  let C : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c 2 z.2 z.1
  let Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := fun z =>
    rampHorizontalCovariantDerivative D (fun s => c z.1 s) (fun s => H (z.1, s)) z.2
  let A : ℝ → ℝ := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
  let As := m62ArcDerivative F c t A
  let N : ℝ → ℝ := fun y => (F.metric t).inner (c y t) (H (y, t)) (B (y, t))
  let P : ℝ → ℝ := fun y => (F.metric t).inner (c y t) (S (y, t)) (B (y, t))
  let CP : ℝ → ℝ := fun y => (F.metric t).inner (c y t) (C (y, t)) (B (y, t))
  let L : ℝ → ℝ := fun y => (F.metric t).inner (c y t) (Y (y, t)) (B (y, t))
  let beta := m63CurvatureJetSquared F c 1 t x
  let chi := m63CurvatureJetSquared F c 2 t x
  let EB : ℝ → ℝ := fun y => R (c y t) ![H (y, t), S (y, t), B (y, t), S (y, t)] -
    2 * T (c y t) ![S (y, t), S (y, t), B (y, t)] +
    T (c y t) ![B (y, t), S (y, t), S (y, t)]
  let EC := R (c x t) ![H (x, t), S (x, t), C (x, t), S (x, t)] -
    2 * T (c x t) ![S (x, t), S (x, t), C (x, t)] +
    T (c x t) ![C (x, t), S (x, t), S (x, t)]
  let E1 := J (c x t) ![S (x, t), H (x, t), S (x, t), B (x, t), S (x, t)] +
    R (c x t) ![B (x, t), S (x, t), B (x, t), S (x, t)] +
    R (c x t) ![H (x, t), S (x, t), B (x, t), H (x, t)] -
    2 * U (c x t) ![S (x, t), S (x, t), S (x, t), B (x, t)] +
    U (c x t) ![S (x, t), B (x, t), S (x, t), S (x, t)] -
    2 * T (c x t) ![H (x, t), S (x, t), B (x, t)] -
    2 * T (c x t) ![S (x, t), H (x, t), B (x, t)] +
    2 * T (c x t) ![B (x, t), S (x, t), H (x, t)]
  let E := J (c x t) ![S (x, t), H (x, t), S (x, t), B (x, t), S (x, t)] +
    R (c x t) ![B (x, t), S (x, t), B (x, t), S (x, t)] +
    2 * R (c x t) ![H (x, t), S (x, t), B (x, t), H (x, t)] -
    2 * U (c x t) ![S (x, t), S (x, t), S (x, t), B (x, t)] +
    U (c x t) ![S (x, t), B (x, t), S (x, t), S (x, t)] -
    3 * T (c x t) ![H (x, t), S (x, t), B (x, t)] -
    3 * T (c x t) ![S (x, t), H (x, t), B (x, t)] +
    3 * T (c x t) ![B (x, t), S (x, t), H (x, t)]
  change (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun s => c x s)
        (fun s => m63CurvatureJet F c 1 s x) t) (B (x, t)) =
    (F.metric t).inner (c x t) (m63CurvatureJet F c 3 t x) (B (x, t)) +
      3 * A x * beta + 3 * As x * N x + m62ArcSecondDerivative F c t A x * P x + E
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hS := unitTangent_joint_contMDiff F c hc
  have hH := M63.curvatureJet_joint_contMDiff F c hc 0
  have hB := M63.curvatureJet_joint_contMDiff F c hc 1
  have hC := M63.curvatureJet_joint_contMDiff F c hc 2
  have hY := m63FixedPullback_time_joint_contMDiff D c H hopen hc.joint_smooth hH
  have hA : ContDiff ℝ ∞ A :=
    (normalization_coefficient_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hAs : ContDiff ℝ ∞ As :=
    (hv.inv (fun y => (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne')).mul
      (contDiff_infty_iff_deriv.mp hA).2
  have hN : ContDiff ℝ ∞ N :=
    (metric_pairing_contDiffOn F c hc.joint_smooth H B hH hB).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hP : ContDiff ℝ ∞ P :=
    (metric_pairing_contDiffOn F c hc.joint_smooth S B hS hB).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hCP : ContDiff ℝ ∞ CP :=
    (metric_pairing_contDiffOn F c hc.joint_smooth C B hC hB).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hambient := m63CurvatureAmbientPair_firstJet_derivative F c hc ht x
  change DifferentiableAt ℝ EB x ∧ m62ArcDerivative F c t EB x = EC + E1 at hambient
  have hidentity (y : ℝ) : L y = CP y + 2 * A y * N y + As y * P y + EB y := by
    have h := m63CurvatureVector_time_pair F c hc ht y (B (y, t))
    change L y = CP y + 2 * A y * N y + As y * P y +
      R (c y t) ![H (y, t), S (y, t), B (y, t), S (y, t)] -
      2 * T (c y t) ![S (y, t), S (y, t), B (y, t)] +
      T (c y t) ![B (y, t), S (y, t), S (y, t)] at h
    dsimp only [EB]
    linarith only [h]
  have htestC : (F.metric t).inner (c x t) (Y (x, t)) (C (x, t)) =
      chi + 2 * A x * (F.metric t).inner (c x t) (H (x, t)) (C (x, t)) +
        As x * (F.metric t).inner (c x t) (S (x, t)) (C (x, t)) + EC := by
    have h := m63CurvatureVector_time_pair F c hc ht x (C (x, t))
    change (F.metric t).inner (c x t) (Y (x, t)) (C (x, t)) =
      chi + 2 * A x * (F.metric t).inner (c x t) (H (x, t)) (C (x, t)) +
        As x * (F.metric t).inner (c x t) (S (x, t)) (C (x, t)) +
        R (c x t) ![H (x, t), S (x, t), C (x, t), S (x, t)] -
        2 * T (c x t) ![S (x, t), S (x, t), C (x, t)] +
        T (c x t) ![C (x, t), S (x, t), S (x, t)] at h
    dsimp only [EC]
    linarith only [h]
  have hRHS : m62ArcDerivative F c t
      (fun y => CP y + 2 * A y * N y + As y * P y + EB y) x =
      m62ArcDerivative F c t CP x + 2 * As x * N x +
        2 * A x * m62ArcDerivative F c t N x +
        m62ArcSecondDerivative F c t A x * P x +
        As x * m62ArcDerivative F c t P x + m62ArcDerivative F c t EB x := by
    have hd : HasDerivAt (fun y => CP y + 2 * A y * N y + As y * P y + EB y)
        (deriv CP x + (2 * deriv A x * N x + 2 * A x * deriv N x) +
          (deriv As x * P x + As x * deriv P x) + deriv EB x) x :=
      ((((hCP.differentiable (by simp) x).hasDerivAt.add
        (((hA.differentiable (by simp) x).hasDerivAt.const_mul 2).mul
          (hN.differentiable (by simp) x).hasDerivAt)).add
        ((hAs.differentiable (by simp) x).hasDerivAt.mul
          (hP.differentiable (by simp) x).hasDerivAt)).add hambient.1.hasDerivAt)
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [As, m62ArcSecondDerivative, m62ArcDerivative]
    ring
  have hCPair := m63ArcDerivative_metric_pairing F c hc C B hC hB ht x
  change m62ArcDerivative F c t CP x =
    (F.metric t).inner (c x t) (m63CurvatureJet F c 3 t x) (B (x, t)) + chi at hCPair
  have hNPair := m63ArcDerivative_metric_pairing F c hc H B hH hB ht x
  change m62ArcDerivative F c t N x =
    beta + (F.metric t).inner (c x t) (H (x, t)) (C (x, t)) at hNPair
  have hPPair := m63ArcDerivative_metric_pairing F c hc S B hS hB ht x
  change m62ArcDerivative F c t P x =
    N x + (F.metric t).inner (c x t) (S (x, t)) (C (x, t)) at hPPair
  have hLPair := m63ArcDerivative_metric_pairing F c hc Y B hY hB ht x
  change m62ArcDerivative F c t L x =
    (F.metric t).inner (c x t) (m62SpatialDerivative F c t (fun y => Y (y, t)) x)
      (B (x, t)) + (F.metric t).inner (c x t) (Y (x, t)) (C (x, t)) at hLPair
  rw [show L = (fun y => CP y + 2 * A y * N y + As y * P y + EB y) from funext hidentity,
    hRHS, hCPair, hNPair, hPPair, hambient.2] at hLPair
  have hspatial : (F.metric t).inner (c x t)
      (m62SpatialDerivative F c t (fun y => Y (y, t)) x) (B (x, t)) =
      (F.metric t).inner (c x t) (m63CurvatureJet F c 3 t x) (B (x, t)) +
        2 * A x * beta + 3 * As x * N x + m62ArcSecondDerivative F c t A x * P x + E1 := by
    nlinarith only [hLPair, htestC]
  have hcomm := m63SpatialDerivative_time_commutator_pair F c hc H hH ht x (B (x, t))
  change (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun s => c x s)
        (fun s => m63CurvatureJet F c 1 s x) t) (B (x, t)) =
    (F.metric t).inner (c x t) (m62SpatialDerivative F c t (fun y => Y (y, t)) x)
      (B (x, t)) + A x * beta +
      R (c x t) ![H (x, t), S (x, t), B (x, t), H (x, t)] -
      T (c x t) ![S (x, t), H (x, t), B (x, t)] -
      T (c x t) ![H (x, t), S (x, t), B (x, t)] +
      T (c x t) ![B (x, t), S (x, t), H (x, t)] at hcomm
  rw [hspatial] at hcomm
  dsimp only [E1, E] at hcomm ⊢
  rw [hcomm]
  ring

end PoincareConjecture
