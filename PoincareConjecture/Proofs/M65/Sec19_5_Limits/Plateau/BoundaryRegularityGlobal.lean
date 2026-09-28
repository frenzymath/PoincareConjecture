import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.AttainmentIdentities
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularitySemicircle











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex Bundle
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

private theorem boundary_inverse_data {p : ℂ} (hp : ‖p‖ = 1) :
    diskBoundaryInverse p (orthonormalBasisOneI.repr p) = 0 ∧
      ContDiffAt ℝ 1 (diskBoundaryInverse p) (orthonormalBasisOneI.repr p) ∧
      ∀ w : LoopPlane, w ≠ 0 →
        diskBoundaryCoordinate p (diskBoundaryInverse p w) = w := by
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [diskBoundaryInverse, M65StrictTrace.boundaryInverse, hp0]
  · let E := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    have h : ContDiffAt ℝ 1 (M65StrictTrace.boundaryInverse p) p :=
      ((M65StrictTrace.contDiffAt_boundaryInverse hp0).restrict_scalars ℝ).of_le (by simp)
    have h' := E.contDiff.contDiffAt.comp p h
    have h'' : ContDiffAt ℝ 1 (E ∘ M65StrictTrace.boundaryInverse p)
        (E.symm (E p)) := by simpa only [ContinuousLinearEquiv.symm_apply_apply] using h'
    exact h''.comp (E p) E.symm.contDiff.contDiffAt
  · intro w hw
    have hw' : orthonormalBasisOneI.repr.symm w ≠ 0 := by
      intro hh
      exact hw (orthonormalBasisOneI.repr.symm.injective (by simpa using hh))
    simp only [diskBoundaryCoordinate, diskBoundaryInverse,
      LinearIsometryEquiv.symm_apply_apply,
      M65StrictTrace.boundaryCoordinate_inverse hp0 hw',
      LinearIsometryEquiv.apply_symm_apply]

private def diskTraceExtension {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (f : LoopPlane → M) (z : LoopPlane) : M :=
  if hz : ‖z‖ = 1 then γ (F.parameter ⟨z, hz⟩) else f z

private theorem diskTraceExtension_eqOn {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (f : LoopPlane → M) :
    EqOn (diskTraceExtension F f) f (ball (0 : LoopPlane) 1) := by
  intro z hz
  exact dif_neg (ne_of_lt (mem_ball_zero_iff.mp hz))

private theorem diskTraceExtension_trace {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (f : LoopPlane → M) (z : LoopCircle) :
    diskTraceExtension F f z = γ (F.parameter z) := by
  simp only [diskTraceExtension, dif_pos z.property]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

private theorem planeTension_eq_of_eqOn {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) {f q : LoopPlane → M} {U : Set LoopPlane}
    (hU : IsOpen U) (heq : EqOn q f U) {z : LoopPlane} (hz : z ∈ U) :
    m65PlaneTension D q z = m65PlaneTension D f z := by
  have hd (w : LoopPlane) (hw : w ∈ U) :
      mfderiv (𝓡 2) (𝓡 3) q w = mfderiv (𝓡 2) (𝓡 3) f w :=
    (heq.eventuallyEq_of_mem (hU.mem_nhds hw)).mfderiv_eq
  unfold m65PlaneTension
  apply Finset.sum_congr rfl
  intro i _
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hline : Tendsto (fun r : ℝ => z + r • v) (𝓝 0) (𝓝 z) := by
    have hh : Continuous (fun r : ℝ => z + r • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using
      hh.tendsto (0 : ℝ)
  have hnear := hline.eventually (hU.mem_nhds hz)
  have hcurve : (fun r : ℝ => q (z + r • v)) =ᶠ[𝓝 0]
      (fun r : ℝ => f (z + r • v)) := hnear.mono fun r hr => heq hr
  have hvelocity : curveVelocity (n := 3) (fun r : ℝ => q (z + r • v)) 0 =
      curveVelocity (n := 3) (fun r : ℝ => f (z + r • v)) 0 := by
    unfold curveVelocity
    rw [hcurve.mfderiv_eq]
    rfl
  let E := trivializationAt LoopAmbient (TangentSpace (𝓡 3) : M → Type _) (f z)
  have hcoeff :
      (fun r : ℝ => (E ⟨q (z + r • v), mfderiv (𝓡 2) (𝓡 3) q (z + r • v) v⟩).2)
        =ᶠ[𝓝 0]
      (fun r : ℝ => (E ⟨f (z + r • v), mfderiv (𝓡 2) (𝓡 3) f (z + r • v) v⟩).2) := by
    filter_upwards [hnear] with r hr
    rw [heq hr, hd _ hr]
  change rampHorizontalCovariantDerivative D (fun r => q (z + r • v))
      (fun r => mfderiv (𝓡 2) (𝓡 3) q (z + r • v) v) 0 =
    rampHorizontalCovariantDerivative D (fun r => f (z + r • v))
      (fun r => mfderiv (𝓡 2) (𝓡 3) f (z + r • v) v) 0
  have hpoint : q (z + (0 : ℝ) • v) = f (z + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using heq hz
  have hcolumn : mfderiv (𝓡 2) (𝓡 3) q (z + (0 : ℝ) • v) v =
      mfderiv (𝓡 2) (𝓡 3) f (z + (0 : ℝ) • v) v := by
    exact congrArg (fun A : LoopPlane →L[ℝ] LoopAmbient => A v)
      (hd _ (by simpa only [zero_smul, add_zero] using hz))
  simp only [rampHorizontalCovariantDerivative, hvelocity, zero_smul, add_zero, heq hz]
  apply congrArg₂ (fun a b : LoopAmbient => a + b)
  · exact congrArg₂ (fun (p : M) (a : LoopAmbient) =>
      (E.symmL ℝ p : LoopAmbient →L[ℝ] LoopAmbient) a) hpoint hcoeff.deriv_eq
  · exact congrArg₂ (fun (p : M) (a : LoopAmbient) =>
      (D.connection (FiberBundle.extend LoopAmbient (show TangentSpace (𝓡 3) p from a)) p
        (show TangentSpace (𝓡 3) p from
          curveVelocity (n := 3) (fun r : ℝ => f (z + r • v)) 0) : LoopAmbient)) hpoint hcolumn

private theorem interiorRepresentative_congr {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {F : M65WeakDisk e γ} {f q : LoopPlane → M}
    (hf : M65InteriorDiskRepresentative D F f)
    (heq : EqOn q f (ball (0 : LoopPlane) 1)) :
    M65InteriorDiskRepresentative D F q := by
  refine ⟨hf.smooth.congr heq, ?_, ?_, ?_⟩
  · have hh : q =ᵐ[volume.restrict (ball (0 : LoopPlane) 1)] f :=
      (ae_restrict_mem isOpen_ball.measurableSet).mono heq
    exact hh.trans hf.value_ae
  · intro i
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet, hf.derivative_ae i]
      with z hz hzi
    have hh : (e ∘ q) =ᶠ[𝓝 z] (e ∘ f) :=
      (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).fun_comp e
    rw [hh.fderiv_eq]
    exact hzi
  · intro z hz
    rw [planeTension_eq_of_eqOn D isOpen_ball heq hz]
    exact hf.harmonic z hz

omit [IsManifold (𝓡 3) ∞ M] in
private theorem diskTraceExtension_local {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (f : LoopPlane → M)
    {p : ℂ} (hp : ‖p‖ = 1) {r : ℝ} (hr : 0 < r) (q : LoopPlane → M)
    (hq : ContMDiffOn (𝓡 2) (𝓡 3) 1 q
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))
    (heq : EqOn q (f ∘ diskBoundaryCoordinate p)
      (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}))
    (htrace : ∀ t ∈ Icc (-r) r, q (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      γ (F.parameter (boundaryCirclePoint hp t))) :
    ContMDiffWithinAt (𝓡 2) (𝓡 3) 1 (diskTraceExtension F f)
      loopDiskSet (orthonormalBasisOneI.repr p) := by
  let z := orthonormalBasisOneI.repr p
  let Q := diskBoundaryInverse p
  let K := closedBall (0 : LoopPlane) r ∩ {w | 0 ≤ w 1}
  obtain ⟨hQ0, hQ, hright⟩ := boundary_inverse_data hp
  change Q z = 0 at hQ0
  have hz : ‖z‖ = 1 := by simpa only [z, LinearIsometryEquiv.norm_map] using hp
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hsmall : ∀ᶠ w in 𝓝 z, Q w ∈ ball (0 : LoopPlane) r := by
    have hh : ball (0 : LoopPlane) r ∈ 𝓝 (Q z) := by
      rw [hQ0]
      exact ball_mem_nhds _ hr
    exact hQ.continuousAt.tendsto.eventually hh
  have hnonzero : ∀ᶠ w in 𝓝 z, w ≠ 0 := isOpen_ne.mem_nhds hz0
  have hdata : ∀ᶠ w in 𝓝[loopDiskSet] z,
      diskBoundaryCoordinate p (Q w) = w ∧ Q w ∈ ball (0 : LoopPlane) r ∧ 0 ≤ Q w 1 := by
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      hnonzero.filter_mono nhdsWithin_le_nhds] with w hw hwr hw0
    have hrightw := hright w hw0
    refine ⟨hrightw, hwr, ?_⟩
    have hn : Real.exp (-(Q w) 1) ≤ 1 := by
      rw [← norm_diskBoundaryCoordinate hp, hrightw]
      exact mem_closedBall_zero_iff.mp hw
    exact neg_nonpos.mp (Real.exp_le_one_iff.mp hn)
  have hlocal : (diskTraceExtension F f) =ᶠ[𝓝[loopDiskSet] z] (q ∘ Q) := by
    filter_upwards [hdata, self_mem_nhdsWithin] with w hw hwD
    rcases hw with ⟨hP, hwr, hwy⟩
    by_cases hw1 : ‖w‖ = 1
    · have hy0 : Q w 1 = 0 := by
        have hh : Real.exp (-(Q w) 1) = 1 := by
          rw [← norm_diskBoundaryCoordinate hp, hP, hw1]
        have hh' : -(Q w) 1 = 0 := Real.exp_injective (by simpa using hh)
        exact neg_eq_zero.mp hh'
      have haxis : Q w = Q w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
        ext i
        fin_cases i <;> simp [EuclideanSpace.basisFun_apply, hy0]
      have hcoord : |Q w 0| < r := by
        have hh := mem_ball_zero_iff.mp hwr
        rw [haxis, norm_smul, Real.norm_eq_abs,
          (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one] at hh
        exact hh
      have ht : Q w 0 ∈ Icc (-r) r := ⟨(abs_lt.mp hcoord).1.le, (abs_lt.mp hcoord).2.le⟩
      have hcircle : boundaryCirclePoint hp (Q w 0) = (⟨w, hw1⟩ : LoopCircle) := by
        apply Subtype.ext
        change diskBoundaryCoordinate p (Q w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0) = w
        rw [← haxis, hP]
      change diskTraceExtension F f w = q (Q w)
      rw [diskTraceExtension, dif_pos hw1, haxis, htrace _ ht, hcircle]
    · have hn : ‖w‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp hwD) hw1
      have hy : 0 < Q w 1 := by
        have hh : Real.exp (-(Q w) 1) < 1 := by
          rw [← norm_diskBoundaryCoordinate hp, hP]
          exact hn
        exact neg_neg_iff_pos.mp (Real.exp_lt_one_iff.mp hh)
      change diskTraceExtension F f w = q (Q w)
      rw [diskTraceExtension, dif_neg hw1]
      simpa only [Function.comp_apply, hP] using (heq ⟨hwr, hy⟩).symm
  have hK : Q ⁻¹' K ∈ 𝓝[loopDiskSet] z := hdata.mono fun w hw =>
    ⟨ball_subset_closedBall hw.2.1, hw.2.2⟩
  have hqQ : ContMDiffWithinAt (𝓡 2) (𝓡 3) 1 q K (Q z) := by
    rw [hQ0]
    exact hq 0 ⟨mem_closedBall_self hr.le, by simp⟩
  have hcomp := hqQ.comp' z
    (hQ.contMDiffAt.contMDiffWithinAt (s := loopDiskSet))
  have hcomp' : ContMDiffWithinAt (𝓡 2) (𝓡 3) 1 (q ∘ Q) loopDiskSet z :=
    hcomp.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hK)
  exact hcomp'.congr_of_eventuallyEq_of_mem hlocal (by
    change ‖z - 0‖ ≤ 1
    simp only [sub_zero, hz, le_refl])





theorem exists_global_boundary_extension {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    {g : RiemannianMetric 3 M} (connection : LeviCivitaData g)
    (F : M65WeakDisk e γ) (f : LoopPlane → M)
    (hf : M65InteriorDiskRepresentative connection F f)
    (hlocal : ∀ (p : ℂ) (hp : ‖p‖ = 1), ∃ (r : ℝ) (_hr : 0 < r) (q : LoopPlane → M),
      ContMDiffOn (𝓡 2) (𝓡 3) 1 q (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
      EqOn q (f ∘ diskBoundaryCoordinate p) (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      ∀ t ∈ Icc (-r) r, q (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        γ (F.parameter (boundaryCirclePoint hp t))) :
    ∃ fbar : LoopPlane → M, EqOn fbar f (ball (0 : LoopPlane) 1) ∧
      M65InteriorDiskRepresentative connection F fbar ∧
      ContMDiffOn (𝓡 2) (𝓡 3) 1 fbar loopDiskSet ∧
      ∀ z : LoopCircle, fbar z = γ (F.parameter z) := by
  let fbar := diskTraceExtension F f
  have heq := diskTraceExtension_eqOn F f
  refine ⟨fbar, heq, interiorRepresentative_congr hf heq, ?_, diskTraceExtension_trace F f⟩
  intro z hz
  by_cases hzi : ‖z‖ < 1
  · have hzB : z ∈ ball (0 : LoopPlane) 1 := mem_ball_zero_iff.mpr hzi
    have hs : ContMDiffAt (𝓡 2) (𝓡 3) 1 f z :=
      ((hf.smooth z hzB).contMDiffAt (isOpen_ball.mem_nhds hzB)).of_le (by simp)
    exact (hs.congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzB))).contMDiffWithinAt
  · have hzn : ‖z‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hz) (le_of_not_gt hzi)
    let p := orthonormalBasisOneI.repr.symm z
    have hp : ‖p‖ = 1 := by simpa only [p, LinearIsometryEquiv.norm_map] using hzn
    obtain ⟨r, hr, q, hq, hqeq, htrace⟩ := hlocal p hp
    have hh := diskTraceExtension_local F f hp hr q hq hqeq htrace
    simpa only [p, LinearIsometryEquiv.apply_symm_apply] using hh

end PoincareConjecture.M65Boundary
