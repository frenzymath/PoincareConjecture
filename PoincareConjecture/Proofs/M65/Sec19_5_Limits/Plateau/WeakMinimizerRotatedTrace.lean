import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerRotation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryGraph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace PoincareConjecture

def m65DiskRotationL2 (θ : ℝ) :
    Lp ℝ 2 (volume.restrict loopDiskSet) →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict loopDiskSet) :=
  Lp.compMeasurePreservingₗᵢ ℝ (m65PlaneRotation θ) (m65PlaneRotation_disk_measurePreserving θ)

def m65BoundaryRotationL2 (θ : ℝ) : Lp ℝ 2 m65CircleBoundaryMeasure →ₗᵢ[ℝ]
    Lp ℝ 2 m65CircleBoundaryMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (m65PlaneRotation θ)
    (m65PlaneRotation_boundary_measurePreserving θ)

private theorem m65Rotation_basis (θ : ℝ) :
    m65PlaneRotation θ (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      Real.cos θ • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        Real.sin θ • EuclideanSpace.basisFun (Fin 2) ℝ 1 ∧
    m65PlaneRotation θ (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -Real.sin θ • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        Real.cos θ • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  have h0 : EuclideanSpace.basisFun (Fin 2) ℝ 0 = Proofs.M58.angularPoint 0 := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  have h1 : EuclideanSpace.basisFun (Fin 2) ℝ 1 = Proofs.M58.angularPoint (Real.pi / 2) := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  constructor
  · rw [h0, m65PlaneRotation_angular]
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  · rw [h1, m65PlaneRotation_angular]
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply,
      Real.cos_add, Real.sin_add]

private theorem m65Rotation_derivative (θ : ℝ) (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (z : LoopPlane) (i : Fin 2) :
    fderiv ℝ (f ∘ m65PlaneRotation θ) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      (![Real.cos θ * fderiv ℝ f (m65PlaneRotation θ z)
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        Real.sin θ * fderiv ℝ f (m65PlaneRotation θ z)
          (EuclideanSpace.basisFun (Fin 2) ℝ 1),
        -Real.sin θ * fderiv ℝ f (m65PlaneRotation θ z)
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        Real.cos θ * fderiv ℝ f (m65PlaneRotation θ z)
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)] : Fin 2 → ℝ) i := by
  have h := ((hf.differentiable one_ne_zero (m65PlaneRotation θ z)).hasFDerivAt).comp z
    (m65PlaneRotation θ).toContinuousLinearEquiv.hasFDerivAt
  rw [h.fderiv]
  fin_cases i
  · change fderiv ℝ f (m65PlaneRotation θ z)
        (m65PlaneRotation θ (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
      Real.cos θ * fderiv ℝ f (m65PlaneRotation θ z) (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        Real.sin θ * fderiv ℝ f (m65PlaneRotation θ z) (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    rw [(m65Rotation_basis θ).1, map_add, map_smul, map_smul]
    rfl
  · change fderiv ℝ f (m65PlaneRotation θ z)
        (m65PlaneRotation θ (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      -Real.sin θ * fderiv ℝ f (m65PlaneRotation θ z) (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        Real.cos θ * fderiv ℝ f (m65PlaneRotation θ z) (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    rw [(m65Rotation_basis θ).2, map_add, map_smul, map_smul]
    rfl

theorem m65DiskRotationL2_energy (θ : ℝ)
    (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) :
    ‖Real.cos θ • m65DiskRotationL2 θ (d 0) +
      Real.sin θ • m65DiskRotationL2 θ (d 1)‖ ^ 2 +
    ‖-Real.sin θ • m65DiskRotationL2 θ (d 0) +
      Real.cos θ • m65DiskRotationL2 θ (d 1)‖ ^ 2 = ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 := by
  rw [norm_add_sq_real, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq,
    real_inner_smul_left, real_inner_smul_right, LinearIsometry.norm_map]
  have h := Real.cos_sq_add_sin_sq θ
  nlinarith [congrArg (fun a => a * ‖d 0‖ ^ 2) h,
    congrArg (fun a => a * ‖d 1‖ ^ 2) h]

private theorem m65RotatedC1_trace (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (u : Lp ℝ 2 (volume.restrict loopDiskSet))
    (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hu : u =ᵐ[volume.restrict loopDiskSet] f)
    (hd : ∀ i, d i =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hb : b =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => f (Proofs.M58.angularPoint t)) : M65DiskWeakTrace u d b := by
  have hfa := (Lp.memLp u).ae_eq hu
  have hfd (i : Fin 2) := (Lp.memLp (d i)).ae_eq (hd i)
  have hfb := (Lp.memLp b).ae_eq hb
  have hu' : hfa.toLp f = u := Lp.ext (hfa.coeFn_toLp.trans hu.symm)
  have hd' : (fun i => (hfd i).toLp
      (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = d := by
    funext i
    exact Lp.ext ((hfd i).coeFn_toLp.trans (hd i).symm)
  have hb' : hfb.toLp (fun t => f (Proofs.M58.angularPoint t)) = b :=
    Lp.ext (hfb.coeFn_toLp.trans hb.symm)
  have h := m65DiskWeakTrace_of_C1 f hf hfa hfd hfb
  rwa [hu', hd', hb'] at h

theorem m65WeakTrace_rotation (θ : ℝ)
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b)) :
    M65DiskWeakTrace (m65DiskRotationL2 θ u)
      ![Real.cos θ • m65DiskRotationL2 θ (d 0) + Real.sin θ • m65DiskRotationL2 θ (d 1),
        -Real.sin θ • m65DiskRotationL2 θ (d 0) + Real.cos θ • m65DiskRotationL2 θ (d 1)]
      (m65CircleBoundaryPullback (m65BoundaryRotationL2 θ b)) := by
  obtain ⟨f, A, B, C, hf, hA, hB, hC, hAlim, hBlim, hClim⟩ :=
    m65WeakTrace_exists_smooth_boundary_graph htrace
  let Q := m65PlaneRotation θ
  let T := m65DiskRotationL2 θ
  let S := m65BoundaryRotationL2 θ
  let D (w : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) :=
    ![Real.cos θ • T (w 0) + Real.sin θ • T (w 1),
      -Real.sin θ • T (w 0) + Real.cos θ • T (w 1)]
  let V (w : Fin 2 → LoopPlane → ℝ) (z : LoopPlane) :=
    ![Real.cos θ * w 0 (Q z) + Real.sin θ * w 1 (Q z),
      -Real.sin θ * w 0 (Q z) + Real.cos θ * w 1 (Q z)]
  have hT (w : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      T w =ᵐ[volume.restrict loopDiskSet] fun z => w (Q z) :=
    Lp.coeFn_compMeasurePreserving w (m65PlaneRotation_disk_measurePreserving θ)
  have hS (w : Lp ℝ 2 m65CircleBoundaryMeasure) :
      S w =ᵐ[m65CircleBoundaryMeasure] fun z => w (Q z) :=
    Lp.coeFn_compMeasurePreserving w (m65PlaneRotation_boundary_measurePreserving θ)
  have hD (w : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) (i : Fin 2) :
      D w i =ᵐ[volume.restrict loopDiskSet] fun z => V (fun k => (w k : LoopPlane → ℝ)) z i := by
    fin_cases i
    · filter_upwards [Lp.coeFn_add (Real.cos θ • T (w 0)) (Real.sin θ • T (w 1)),
        Lp.coeFn_smul (Real.cos θ) (T (w 0)), Lp.coeFn_smul (Real.sin θ) (T (w 1)),
        hT (w 0), hT (w 1)] with z hz h0 h1 ht0 ht1
      change (Real.cos θ • T (w 0) + Real.sin θ • T (w 1) : Lp ℝ 2 _) z = _
      rw [hz, Pi.add_apply, h0, h1, Pi.smul_apply, Pi.smul_apply, ht0, ht1]
      rfl
    · filter_upwards [Lp.coeFn_add (-Real.sin θ • T (w 0)) (Real.cos θ • T (w 1)),
        Lp.coeFn_smul (-Real.sin θ) (T (w 0)), Lp.coeFn_smul (Real.cos θ) (T (w 1)),
        hT (w 0), hT (w 1)] with z hz h0 h1 ht0 ht1
      change (-Real.sin θ • T (w 0) + Real.cos θ • T (w 1) : Lp ℝ 2 _) z = _
      rw [hz, Pi.add_apply, h0, h1, Pi.smul_apply, Pi.smul_apply, ht0, ht1]
      rfl
  have hTA (n : ℕ) : T (A n) =ᵐ[volume.restrict loopDiskSet] f n ∘ Q :=
    (hT (A n)).trans ((m65PlaneRotation_disk_measurePreserving θ).quasiMeasurePreserving.ae (hA n))
  have hTB (n : ℕ) (i : Fin 2) : D (B n) i =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ (f n ∘ Q) z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    filter_upwards [hD (B n) i,
      (m65PlaneRotation_disk_measurePreserving θ).quasiMeasurePreserving.ae (hB n 0),
      (m65PlaneRotation_disk_measurePreserving θ).quasiMeasurePreserving.ae (hB n 1)]
      with z hz h0 h1
    rw [hz]
    dsimp only [V]
    rw [h0, h1, m65Rotation_derivative θ (f n) ((hf n).of_le (by simp)) z i]
  have hSC (n : ℕ) : S (C n) =ᵐ[m65CircleBoundaryMeasure] f n ∘ Q :=
    (hS (C n)).trans
      ((m65PlaneRotation_boundary_measurePreserving θ).quasiMeasurePreserving.ae (hC n))
  have hPC (n : ℕ) : m65CircleBoundaryPullback (S (C n)) =ᵐ[
      volume.restrict (Icc (-Real.pi) Real.pi)]
        fun t => f n (Q (Proofs.M58.angularPoint t)) :=
    (m65CircleBoundaryPullback_coe (S (C n))).trans
      (ae_of_ae_map Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable (hSC n))
  have hfQ (n : ℕ) : ContDiff ℝ 1 (f n ∘ Q) :=
    ((hf n).of_le (by simp)).comp Q.toContinuousLinearEquiv.contDiff
  have htraces (n : ℕ) : M65DiskWeakTrace (T (A n)) (D (B n))
      (m65CircleBoundaryPullback (S (C n))) :=
    m65RotatedC1_trace (f n ∘ Q) (hfQ n) (T (A n)) (D (B n))
      (m65CircleBoundaryPullback (S (C n))) (hTA n) (hTB n) (hPC n)
  have hTlim (i : Fin 2) : Tendsto (fun n => T (B n i)) atTop (𝓝 (T (d i))) :=
    (T.continuous.tendsto (d i)).comp (hBlim i)
  have hDlim (i : Fin 2) : Tendsto (fun n => D (B n) i) atTop (𝓝 (D d i)) := by
    fin_cases i
    · exact ((hTlim 0).const_smul (Real.cos θ)).add ((hTlim 1).const_smul (Real.sin θ))
    · exact ((hTlim 0).const_smul (-Real.sin θ)).add ((hTlim 1).const_smul (Real.cos θ))
  exact m65DiskWeakTrace_of_limit htraces ((T.continuous.tendsto u).comp hAlim)
    (fun i v => (hDlim i).inner tendsto_const_nhds)
    ((m65CircleBoundaryPullback.continuous.tendsto (S b)).comp
      ((S.continuous.tendsto b).comp hClim))

end PoincareConjecture
