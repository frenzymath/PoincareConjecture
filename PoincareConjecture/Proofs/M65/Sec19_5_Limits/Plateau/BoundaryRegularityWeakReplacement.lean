import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

open Classical in
private theorem piecewise_memLp {E : Type*} [NormedAddCommGroup E]
    {Z : Set LoopPlane} (hZ : MeasurableSet Z) {f g : LoopPlane → E}
    (hf : MemLp f 2 (volume.restrict Z))
    (hg : MemLp g 2 (volume.restrict loopDiskSet)) :
    MemLp (Z.piecewise f g) 2 (volume.restrict loopDiskSet) := by
  classical
  apply MemLp.piecewise hZ _ (hg.restrict Zᶜ)
  apply hf.mono_measure
  rw [Measure.restrict_restrict hZ]
  exact Measure.restrict_mono_set volume inter_subset_left

open Classical in
private theorem piecewise_integral {Z : Set LoopPlane} (hZ : MeasurableSet Z)
    (hZD : Z ⊆ loopDiskSet) {f g : LoopPlane → ℝ}
    (hf : IntegrableOn f Z) (hg : IntegrableOn g loopDiskSet) :
    (∫ z in loopDiskSet, Z.piecewise f g z) =
      (∫ z in Z, f z) + (∫ z in loopDiskSet, g z) - ∫ z in Z, g z := by
  classical
  have hh := integral_piecewise (μ := volume.restrict loopDiskSet) hZ
    (hf.restrict (t := loopDiskSet)) (hg.integrableOn (s := Zᶜ))
  rw [Measure.restrict_restrict_of_subset hZD, Measure.restrict_restrict hZ.compl,
    inter_comm Zᶜ loopDiskSet, ← Set.sdiff_eq loopDiskSet Z,
    setIntegral_sdiff hZ hg hZD] at hh
  rw [hh]
  ring

private theorem coordinate_pairing {N : ℕ}
    (U : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet))
    {u : LoopPlane → EuclideanSpace ℝ (Fin N)}
    (hu : U =ᵐ[volume.restrict loopDiskSet] u) (j : Fin N) (test : 𝓢(LoopPlane, ℝ)) :
    ⟪m65DiskCoordinateL2 U j, m65DiskTestL2 test⟫_ℝ =
      ∫ z in loopDiskSet, u z j * test z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [m65DiskCoordinateL2_coe U j, hu,
    ((test.memLp 2 volume).restrict loopDiskSet).coeFn_toLp] with z hz hu' ht
  simp only [m65DiskTestL2, hz, hu', ht, Real.inner_apply]

private theorem boundary_pairing (B : Lp ℝ 2 m65CircleBoundaryMeasure)
    {b : ℝ → ℝ}
    (hb : m65CircleBoundaryPullback B =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] b)
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
    ⟪m65CircleBoundaryPullback B, m65DiskBoundaryTestL2 test i⟫_ℝ =
      ∫ t in Icc (-Real.pi) Real.pi, b t * m65DiskBoundaryTest test i t := by
  rw [L2.inner_def]
  have ht : m65DiskBoundaryTestL2 test i =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      m65DiskBoundaryTest test i := by
    unfold m65DiskBoundaryTestL2
    exact MemLp.coeFn_toLp _
  apply integral_congr_ae
  filter_upwards [hb, ht] with t hb' ht'
  simp only [hb', ht', Real.inner_apply]

private theorem green_integrable {N : ℕ} {K : Set LoopPlane}
    {u d : LoopPlane → EuclideanSpace ℝ (Fin N)}
    (hu : MemLp u 2 (volume.restrict K)) (hd : MemLp d 2 (volume.restrict K))
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N) :
    IntegrableOn (fun z => d z j * test z +
      u z j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) K := by
  have h1 := (hd.eval_piLp j).integrable_mul ((test.memLp 2 volume).restrict K)
  have h2 := (hu.eval_piLp j).integrable_mul
    (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test).memLp 2 volume).restrict K)
  simpa +instances only [Pi.add_apply, Pi.mul_apply, IntegrableOn,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using! h1.add h2

end PoincareConjecture.M65Boundary

namespace PoincareConjecture.M65WeakDisk

open M65Boundary

variable {M : Type*} [TopologicalSpace M] {N : ℕ}
  {e : M → EuclideanSpace ℝ (Fin N)} {gamma : LoopCircle → M}

open Classical in




theorem exists_boundary_replacement (F : M65WeakDisk e gamma)
    (he : Continuous e) (hgamma : Continuous gamma)
    {Z : Set LoopPlane} (hZ : IsCompact Z) (hZD : Z ⊆ loopDiskSet)
    (q : LoopPlane → M) (d : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (hq : MemLp (fun z => e (q z)) 2 (volume.restrict Z))
    (hd : ∀ i, MemLp (d i) 2 (volume.restrict Z))
    (B : C(LoopCircle, LoopCircle)) (hB : M65WeakCircleParameter B)
    (hgreen : ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
      (∫ z in Z, (d i z j - F.derivative i z j) * test z +
        (e (q z) j - e (F.value z) j) *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        ∫ t in Icc (-Real.pi) Real.pi,
          (e (gamma (B ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j -
            e (gamma (F.parameter
              ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j) *
              m65DiskBoundaryTest test i t) :
    ∃ G : M65WeakDisk e gamma,
      G.parameter = B ∧
      (∀ z ∈ Z, G.value z = q z) ∧ (∀ z ∉ Z, G.value z = F.value z) ∧
      ∀ i, G.derivative i =ᵐ[volume.restrict loopDiskSet]
        Z.piecewise (d i) (fun z => F.derivative i z) := by
  classical
  let value := Z.piecewise q F.value
  let field (i : Fin 2) := Z.piecewise (d i) (fun z => F.derivative i z)
  have hF : MemLp (fun z => e (F.value z)) 2 (volume.restrict loopDiskSet) :=
    (Lp.memLp F.embeddedValue).ae_eq F.embeddedValue_ae
  have hv : MemLp (fun z => e (value z)) 2 (volume.restrict loopDiskSet) := by
    have hh := piecewise_memLp hZ.measurableSet hq hF
    apply hh.ae_eq
    filter_upwards with z
    by_cases hz : z ∈ Z <;> simp [value, hz]
  have hf (i : Fin 2) : MemLp (field i) 2 (volume.restrict loopDiskSet) :=
    piecewise_memLp hZ.measurableSet (hd i) (Lp.memLp (F.derivative i))
  let U := hv.toLp (fun z => e (value z))
  let D (i : Fin 2) := (hf i).toLp (field i)
  let boundaryValue (j : Fin N) : C(LoopCircle, ℝ) :=
    ⟨fun z => e (gamma (B z)) j,
      (EuclideanSpace.proj j).continuous.comp (he.comp (hgamma.comp B.continuous))⟩
  choose boundary hboundary using fun j => m65CircleBoundary_continuous_class (boundaryValue j)
  have htrace (j : Fin N) : M65DiskWeakTrace (m65DiskCoordinateL2 U j)
      (fun i => m65DiskCoordinateL2 (D i) j) (m65CircleBoundaryPullback (boundary j)) := by
    intro test i
    rw [coordinate_pairing (D i) (hf i).coeFn_toLp j test,
      coordinate_pairing U hv.coeFn_toLp j,
      boundary_pairing (boundary j) (hboundary j) test i]
    let A := fun z => d i z j * test z +
      e (q z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)
    let C := fun z => F.derivative i z j * test z +
      e (F.value z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)
    have hAI : IntegrableOn A Z := green_integrable hq (hd i) test i j
    have hCI : IntegrableOn C loopDiskSet :=
      green_integrable hF (Lp.memLp (F.derivative i)) test i j
    have hvI : IntegrableOn (fun z => e (value z) j *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) loopDiskSet := by
      simpa +instances only [Pi.mul_def, SchwartzMap.lineDerivOp_apply_eq_fderiv,
        IntegrableOn] using! (hv.eval_piLp j).integrable_mul
          (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test).memLp 2 volume).restrict loopDiskSet)
    have hdI : IntegrableOn (fun z => field i z j * test z) loopDiskSet := by
      simpa +instances only [Pi.mul_def, IntegrableOn] using!
        ((hf i).eval_piLp j).integrable_mul ((test.memLp 2 volume).restrict loopDiskSet)
    simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [← integral_add hdI hvI]
    have hpiece : (fun z => field i z j * test z + e (value z) j *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = Z.piecewise A C := by
      funext z
      by_cases hz : z ∈ Z <;> simp [field, value, A, C, hz]
    rw [hpiece, piecewise_integral hZ.measurableSet hZD hAI hCI]
    have hold := F.weak_trace j test i
    rw [coordinate_pairing (F.derivative i) (Filter.EventuallyEq.rfl) j test,
      coordinate_pairing F.embeddedValue F.embeddedValue_ae j,
      boundary_pairing (F.boundary j) (F.boundary_ae j) test i] at hold
    have hoD : IntegrableOn (fun z => F.derivative i z j * test z) loopDiskSet := by
      simpa +instances only [Pi.mul_def, IntegrableOn] using!
        ((Lp.memLp (F.derivative i)).eval_piLp j).integrable_mul
          ((test.memLp 2 volume).restrict loopDiskSet)
    have hoV : IntegrableOn (fun z => e (F.value z) j *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) loopDiskSet := by
      simpa +instances only [Pi.mul_def, SchwartzMap.lineDerivOp_apply_eq_fderiv,
        IntegrableOn] using! (hF.eval_piLp j).integrable_mul
          (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test).memLp 2 volume).restrict loopDiskSet)
    simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv] at hold
    rw [← integral_add hoD hoV] at hold
    let bn := fun t => e (gamma (B
      ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j
    let bo := fun t => e (gamma (F.parameter
      ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j
    have hbn : Continuous bn := (boundaryValue j).continuous.comp
      (Proofs.M58.contDiff_angularPoint.continuous.subtype_mk _)
    have hbo : Continuous bo := (EuclideanSpace.proj j).continuous.comp
      (he.comp (hgamma.comp (F.parameter.continuous.comp
        (Proofs.M58.contDiff_angularPoint.continuous.subtype_mk _))))
    have hbt : Continuous (m65DiskBoundaryTest test i) :=
      (test.continuous.comp Proofs.M58.contDiff_angularPoint.continuous).mul
        ((EuclideanSpace.proj i).continuous.comp Proofs.M58.contDiff_angularPoint.continuous)
    have hnI : IntegrableOn (fun t => bn t * m65DiskBoundaryTest test i t)
        (Icc (-Real.pi) Real.pi) :=
      (hbn.mul hbt).continuousOn.integrableOn_compact isCompact_Icc
    have hoI : IntegrableOn (fun t => bo t * m65DiskBoundaryTest test i t)
        (Icc (-Real.pi) Real.pi) :=
      (hbo.mul hbt).continuousOn.integrableOn_compact isCompact_Icc
    have hdiff := hgreen test i j
    have hdiffA : (fun z => (d i z j - F.derivative i z j) * test z +
        (e (q z) j - e (F.value z) j) *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = fun z => A z - C z := by
      funext z
      dsimp only [A, C]
      ring
    rw [hdiffA, integral_sub hAI (hCI.mono_set hZD)] at hdiff
    change (∫ z in Z, A z) - (∫ z in Z, C z) =
      ∫ t in Icc (-Real.pi) Real.pi, (bn t - bo t) * m65DiskBoundaryTest test i t at hdiff
    simp_rw [sub_mul] at hdiff
    rw [integral_sub hnI hoI] at hdiff
    change (∫ z in loopDiskSet, C z) =
      ∫ t in Icc (-Real.pi) Real.pi, bo t * m65DiskBoundaryTest test i t at hold
    change (∫ z in Z, A z) + (∫ z in loopDiskSet, C z) - (∫ z in Z, C z) =
      ∫ t in Icc (-Real.pi) Real.pi, bn t * m65DiskBoundaryTest test i t
    linarith only [hold, hdiff]
  let G : M65WeakDisk e gamma :=
    { value := value
      embeddedValue := U
      embeddedValue_ae := hv.coeFn_toLp
      derivative := D
      parameter := B
      weakly_monotone := hB
      boundary := boundary
      boundary_ae := hboundary
      weak_trace := htrace }
  refine ⟨G, rfl, ?_, ?_, fun i => (hf i).coeFn_toLp⟩
  · intro z hz
    exact piecewise_eq_of_mem Z q F.value hz
  · intro z hz
    exact piecewise_eq_of_notMem Z q F.value hz

end PoincareConjecture.M65WeakDisk
