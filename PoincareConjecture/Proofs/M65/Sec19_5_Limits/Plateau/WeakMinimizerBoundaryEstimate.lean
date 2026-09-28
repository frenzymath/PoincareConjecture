import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCourantLebesgue
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerRotatedTrace











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

universe u

namespace PoincareConjecture

private theorem m65BoundaryClass_continuous_extension
    (b : C(LoopCircle, ℝ)) (B : Lp ℝ 2 m65CircleBoundaryMeasure)
    (hB : m65CircleBoundaryPullback B =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => b ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩) :
    ∃ f : C(LoopPlane, ℝ), (∀ z : LoopCircle, f z = b z) ∧
      B =ᵐ[m65CircleBoundaryMeasure] f := by
  have hs : IsClosed {z : LoopPlane | ‖z‖ = 1} :=
    isClosed_eq continuous_norm continuous_const
  obtain ⟨f, hf⟩ := ContinuousMap.exists_extension' hs.isClosedEmbedding_subtypeVal b
  have hA := Proofs.M58.contDiff_angularPoint.continuous
  have hfa : MemLp (fun t => f (Proofs.M58.angularPoint t)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq (f.continuous.comp hA).aestronglyMeasurable).mpr
      (((f.continuous.comp hA).pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hfm : MemLp f 2 m65CircleBoundaryMeasure :=
    (memLp_map_measure_iff f.continuous.aestronglyMeasurable hA.measurable.aemeasurable).mpr hfa
  have hrep : m65CircleBoundaryPullback (hfm.toLp f) =ᵐ[
      volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => b ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ := by
    apply (m65CircleBoundaryPullback_coe _).trans
    filter_upwards [ae_of_ae_map hA.measurable.aemeasurable hfm.coeFn_toLp] with t ht
    rw [ht]
    exact congrFun hf ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩
  have heq : B = hfm.toLp f := m65CircleBoundaryPullback.injective
    (Lp.ext (hB.trans hrep.symm))
  exact ⟨f, fun z => congrFun hf z, heq ▸ hfm.coeFn_toLp⟩

private theorem m65BoundaryClass_rotated_endpoint
    (b : C(LoopCircle, ℝ)) (B : Lp ℝ 2 m65CircleBoundaryMeasure)
    (hB : m65CircleBoundaryPullback B =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => b ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)
    (θ : ℝ) {ε R σ : ℝ} (hε : 0 < ε) (hR : R ≤ 1) (hσ : σ = 1 ∨ σ = -1) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      m65BoundaryRotationL2 θ B (Proofs.M58.angularPoint (σ * (2 * m65CrosscutAngle r))) =
        b ⟨Proofs.M58.angularPoint (θ + σ * (2 * m65CrosscutAngle r)),
          Proofs.M58.norm_angularPoint _⟩ := by
  obtain ⟨f, hf, hBf⟩ := m65BoundaryClass_continuous_extension b B hB
  have hrot : m65BoundaryRotationL2 θ B =ᵐ[m65CircleBoundaryMeasure]
      f ∘ m65PlaneRotation θ :=
    (Lp.coeFn_compMeasurePreserving B (m65PlaneRotation_boundary_measurePreserving θ)).trans
      ((m65PlaneRotation_boundary_measurePreserving θ).quasiMeasurePreserving.ae hBf)
  have h := (m65CrosscutBoundaryL2_coe hε hR hσ (m65BoundaryRotationL2 θ B)).symm.trans
    (m65CrosscutBoundaryL2_ae_of_ae hε hR hσ (m65BoundaryRotationL2 θ B)
      (f ∘ m65PlaneRotation θ) hrot)
  filter_upwards [h] with r hr
  rw [hr, Function.comp_apply, m65PlaneRotation_angular]
  exact hf ⟨Proofs.M58.angularPoint (θ + σ * (2 * m65CrosscutAngle r)),
    Proofs.M58.norm_angularPoint _⟩

private theorem m65CoordinateL2_norm_sum {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)) :
    (∑ j, ‖m65DiskCoordinateL2 u j‖ ^ 2) = ‖u‖ ^ 2 := by
  have hi (j : Fin N) : Integrable (fun z => (u z j) ^ 2)
      (volume.restrict loopDiskSet) := ((Lp.memLp u).eval_piLp j).integrable_sq
  calc
    _ = ∑ j, ∫ z in loopDiskSet, (u z j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Lp.norm_sq_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [m65DiskCoordinateL2_coe u j] with z hz
      simp only [hz, Real.norm_eq_abs, sq_abs]
    _ = ∫ z in loopDiskSet, ∑ j, (u z j) ^ 2 :=
      (integral_finsetSum _ (fun j _ => hi j)).symm
    _ = ‖u‖ ^ 2 := by
      rw [Lp.norm_sq_eq_integral_norm_sq]
      congr 1
      funext z
      exact (EuclideanSpace.real_norm_sq_eq (u z)).symm

set_option maxHeartbeats 1200000 in






theorem m65WeakDisk_boundary_courantLebesgue
    {M : Type u} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (he : Continuous e) (hγ : Continuous γ)
    (θ : ℝ) {ε R η : ℝ} (hε : 0 < ε) (hεR : ε < R) (hR : R ≤ 1)
    (hbudget : 2 * Real.pi * (‖F.derivative 0‖ ^ 2 + ‖F.derivative 1‖ ^ 2) <
      η ^ 2 * Real.log (R / ε)) :
    ∃ r ∈ Icc ε R,
      ‖e (γ (F.parameter ⟨Proofs.M58.angularPoint (θ + 2 * m65CrosscutAngle r),
          Proofs.M58.norm_angularPoint _⟩)) -
        e (γ (F.parameter ⟨Proofs.M58.angularPoint (θ - 2 * m65CrosscutAngle r),
          Proofs.M58.norm_angularPoint _⟩))‖ ^ 2 < η ^ 2 := by
  let b (j : Fin N) : C(LoopCircle, ℝ) :=
    ⟨fun z => e (γ (F.parameter z)) j,
      (EuclideanSpace.proj j).continuous.comp (he.comp (hγ.comp F.parameter.continuous))⟩
  let U (j : Fin N) : Lp ℝ 2 (volume.restrict loopDiskSet) :=
    m65DiskRotationL2 θ (m65DiskCoordinateL2 F.embeddedValue j)
  let D (j : Fin N) : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet) :=
    ![Real.cos θ • m65DiskRotationL2 θ (m65DiskCoordinateL2 (F.derivative 0) j) +
        Real.sin θ • m65DiskRotationL2 θ (m65DiskCoordinateL2 (F.derivative 1) j),
      -Real.sin θ • m65DiskRotationL2 θ (m65DiskCoordinateL2 (F.derivative 0) j) +
        Real.cos θ • m65DiskRotationL2 θ (m65DiskCoordinateL2 (F.derivative 1) j)]
  let B (j : Fin N) : Lp ℝ 2 m65CircleBoundaryMeasure :=
    m65BoundaryRotationL2 θ (F.boundary j)
  let P (r : ℝ) := ∀ j : Fin N,
    B j (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) =
      b j ⟨Proofs.M58.angularPoint (θ + 2 * m65CrosscutAngle r),
        Proofs.M58.norm_angularPoint _⟩ ∧
    B j (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r))) =
      b j ⟨Proofs.M58.angularPoint (θ - 2 * m65CrosscutAngle r),
        Proofs.M58.norm_angularPoint _⟩
  have hP : ∀ᵐ r ∂volume.restrict (Icc ε R), P r := by
    apply ae_all_iff.mpr
    intro j
    have hp := m65BoundaryClass_rotated_endpoint (b j) (F.boundary j)
      (F.boundary_ae j) θ hε hR (Or.inl (rfl : (1 : ℝ) = 1))
    have hn := m65BoundaryClass_rotated_endpoint (b j) (F.boundary j)
      (F.boundary_ae j) θ hε hR (Or.inr (rfl : (-1 : ℝ) = -1))
    filter_upwards [hp, hn] with r hp hn
    simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using And.intro hp hn
  have henergy : (∑ j, (‖D j 0‖ ^ 2 + ‖D j 1‖ ^ 2)) =
      ‖F.derivative 0‖ ^ 2 + ‖F.derivative 1‖ ^ 2 := by
    calc
      _ = ∑ j, (‖m65DiskCoordinateL2 (F.derivative 0) j‖ ^ 2 +
          ‖m65DiskCoordinateL2 (F.derivative 1) j‖ ^ 2) :=
        Finset.sum_congr rfl (fun j _ => m65DiskRotationL2_energy θ
          (fun i => m65DiskCoordinateL2 (F.derivative i) j))
      _ = _ := by rw [Finset.sum_add_distrib, m65CoordinateL2_norm_sum, m65CoordinateL2_norm_sum]
  have hrotTrace (j : Fin N) : M65DiskWeakTrace (U j) (D j)
      (m65CircleBoundaryPullback (B j)) := by
    exact m65WeakTrace_rotation θ
      (u := m65DiskCoordinateL2 F.embeddedValue j)
      (d := fun i => m65DiskCoordinateL2 (F.derivative i) j)
      (b := F.boundary j) (F.weak_trace j)
  have hrotBudget : 2 * Real.pi * (∑ j, (‖D j 0‖ ^ 2 + ‖D j 1‖ ^ 2)) <
      η ^ 2 * Real.log (R / ε) := by
    rw [henergy]
    exact hbudget
  obtain ⟨r, hr, hp, hgap⟩ := m65WeakTrace_courantLebesgue U D B
    hrotTrace hε hεR hR hrotBudget P hP
  refine ⟨r, hr, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  have hsum : (∑ j, (B j (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) -
      B j (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r)))) ^ 2) =
      ∑ j, (e (γ (F.parameter ⟨Proofs.M58.angularPoint (θ + 2 * m65CrosscutAngle r),
          Proofs.M58.norm_angularPoint _⟩)) j -
        e (γ (F.parameter ⟨Proofs.M58.angularPoint (θ - 2 * m65CrosscutAngle r),
          Proofs.M58.norm_angularPoint _⟩)) j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [(hp j).1, (hp j).2]
    rfl
  exact hsum ▸ hgap

end PoincareConjecture
