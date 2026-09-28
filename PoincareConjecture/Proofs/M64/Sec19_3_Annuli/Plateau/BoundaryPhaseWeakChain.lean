import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCriticalEmbedding
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakChain
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding

theorem m64WeakPhase_local_memLp_four
    {u : LoopPlane → ℝ} {a : LoopPlane} {r R : ℝ}
    (hrR : r < R) (hu : MemW1p 2 u (ball a R)) :
    MemLp u 4 (volume.restrict (ball a r)) := by
  obtain ⟨chi, hchi, hc, -, hone, hs⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall a r) isOpen_ball (closedBall_subset_ball hrR)
  have hlocal : MemWkp 1 2 u (ball a R ∩ univ) := by
    simpa only [inter_univ] using MemWkp.one_iff_memW1p.mpr hu
  have hglobal :=
    Poincare.Analysis.Sobolev.BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset
      1 isOpen_univ isOpen_ball hlocal hchi hc hs
  have hlow := EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset 1
    isOpen_univ (isClosed_tsupport (fun p => chi p * u p)) hc.mul_right.measure_lt_top.ne
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((4 : ℝ) / 3) by norm_num)
    (show ENNReal.ofReal ((4 : ℝ) / 3) ≤ 2 by norm_num)
    (subset_refl _) hglobal
  have hfour := (TowerStep.MemWkp_subcritical_iterated 0
    (by norm_num : (1 : ℝ) ≤ 4 / 3) (by norm_num : (4 : ℝ) / 3 < (2 : ℕ))
    isOpen_univ hc.mul_right (subset_univ _) hlow).1.memLp
  norm_num [TowerStep.pOne] at hfour
  apply (hfour.restrict (ball a r)).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
  change chi p * u p = u p
  rw [hone p (ball_subset_closedBall hp), one_mul]

theorem m64WeakPhase_scalar_C1_chain
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ} {a : LoopPlane} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : MemLp u 2 (volume.restrict (ball a R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u (ball a R))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ} (hK : 0 < K)
    (hDF : ∀ x, |deriv F x| ≤ K) (i : Fin 2) :
    HasWeakPartialDeriv i (fun p => deriv F (u p) * V i p)
      (fun p => F (u p)) (ball a r) := by
  let R' := (r + R) / 2
  have hr' : r < R' := by dsimp only [R']; linarith
  have hR' : R' < R := by dsimp only [R']; linarith
  have hu4 := m64WeakPhase_local_memLp_four hR' ⟨hu, fun i => ⟨V i, hV i, hw i⟩⟩
  let E := EuclideanSpace ℝ (Fin 1)
  let U : LoopPlane → E := fun p => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => u p)
  let W : Fin 2 → LoopPlane → E := fun i p =>
    (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => V i p)
  let L : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let G := F ∘ L
  have hG : ContDiff ℝ 1 G := hF.comp L.contDiff
  have hderiv (z : E) : fderiv ℝ G z = deriv F (z 0) • L := by
    have hd := ((hF.differentiable (by simp) (z 0)).hasDerivAt.hasFDerivAt).comp z
      L.hasFDerivAt
    apply hd.fderiv.trans
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, smul_eq_mul, L]
    ring
  have hLn : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    change ‖z 0‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using PiLp.norm_apply_le z (0 : Fin 1)
  have hGbound (z : E) : ‖fderiv ℝ G z‖ ≤ K * (1 + ‖z‖ ^ 2) := by
    rw [hderiv, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ K * 1 := mul_le_mul (hDF (z 0)) hLn (norm_nonneg _) hK.le
      _ ≤ _ := by nlinarith [mul_nonneg hK.le (sq_nonneg ‖z‖)]
  have hU : MemLp U 4 (volume.restrict (ball a R')) :=
    MemLp.of_eval_piLp (fun _ => hu4)
  have hW (j : Fin 2) : MemLp (W j) 2 (volume.restrict (ball a R')) :=
    MemLp.of_eval_piLp (fun _ =>
      (hV j).mono_measure (Measure.restrict_mono (ball_subset_ball hR'.le) le_rfl))
  have hweak (j : Fin 2) (b : Fin 1) : HasWeakPartialDeriv j
      (fun p => W j p b) (fun p => U p b) (ball a R') :=
    (hw j).restrict isOpen_ball (ball_subset_ball hR'.le)
  have hc := M60.suWeakPartial_comp_quadratic hr hr' hU hW hweak hG hK hGbound i
  simp only [hderiv, smul_apply, smul_eq_mul] at hc
  exact hc

theorem m64WeakPhase_scalar_C1_column
    {O : Set LoopPlane} (hO : IsOpen O)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u O)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ} (hK : 0 < K)
    (hDF : ∀ x, |deriv F x| ≤ K) {i : Fin 2} {z : LoopPlane → ℝ}
    (hz : MemLp z 2 (volume.restrict O))
    (hwz : HasWeakPartialDeriv i z (fun p => F (u p)) O) :
    z =ᵐ[volume.restrict O] fun p => deriv F (u p) * V i p := by
  classical
  let g := fun p => deriv F (u p) * V i p
  have hg : MemLp g 2 (volume.restrict O) := by
    apply (hV i).of_le_mul (c := K)
      (((hF.continuous_deriv_one).comp_aestronglyMeasurable hu.aestronglyMeasurable).mul
        (hV i).aestronglyMeasurable)
    filter_upwards with p
    change ‖deriv F (u p) * V i p‖ ≤ K * ‖V i p‖
    rw [norm_mul, Real.norm_eq_abs (deriv F (u p))]
    exact mul_le_mul_of_nonneg_right (hDF (u p)) (norm_nonneg _)
  choose R hR hsub using fun a : O => Metric.mem_nhds_iff.mp (hO.mem_nhds a.property)
  let U := fun a : O => ball (a : LoopPlane) (R a / 2)
  have hU (a : O) : IsOpen (U a) := isOpen_ball
  have hmem (a : O) : (a : LoopPlane) ∈ U a := mem_ball_self (half_pos (hR a))
  have hlocal (a : O) : z =ᵐ[volume.restrict (U a)] g := by
    have hle := Measure.restrict_mono (hsub a) (le_rfl : volume ≤ (volume : Measure LoopPlane))
    have hsmall : U a ⊆ O := (ball_subset_ball (half_le_self (hR a).le)).trans (hsub a)
    have hle' := Measure.restrict_mono hsmall (le_rfl : volume ≤ (volume : Measure LoopPlane))
    exact HasWeakPartialDeriv.ae_eq (hU a) (hwz.restrict (hU a) hsmall)
      (m64WeakPhase_scalar_C1_chain (half_pos (hR a)) (half_lt_self (hR a))
        (hu.mono_measure hle) (fun j => (hV j).mono_measure hle)
        (fun j => (hw j).restrict isOpen_ball (hsub a)) hF hK hDF i)
      ((hz.mono_measure hle').locallyIntegrable (by norm_num))
      ((hg.mono_measure hle').locallyIntegrable (by norm_num))
  obtain ⟨T, hT, hcover⟩ := (HereditarilyLindelofSpace.isLindelof O).elim_countable_subcover
    U hU (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_eq_restrict_biUnion_iff U hT z g).mpr fun a _ => hlocal a)

end PoincareConjecture
