import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityWeakMap
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology SchwartzMap LineDeriv

namespace PoincareConjecture.M65Interior

private theorem memLp_piecewise_local {E : Type*} [NormedAddCommGroup E]
    {f g : LoopPlane → E} {K D : Set LoopPlane} [DecidablePred (· ∈ D)]
    (hD : MeasurableSet D)
    (hf : MemLp f 2 (volume.restrict D)) (hg : MemLp g 2 (volume.restrict K)) :
    MemLp (D.piecewise f g) 2 (volume.restrict K) := by
  classical
  apply MemLp.piecewise hD _ (hg.restrict Dᶜ)
  apply hf.mono_measure
  rw [Measure.restrict_restrict hD]
  exact Measure.restrict_mono_set volume inter_subset_left

private theorem integral_piecewise_correction {f g : LoopPlane → ℝ}
    {U D : Set LoopPlane} [DecidablePred (· ∈ D)]
    (hD : MeasurableSet D) (hDU : D ⊆ U)
    (hf : IntegrableOn f D) (hg : IntegrableOn g U) :
    (∫ z in U, D.piecewise f g z) =
      (∫ z in D, f z) + (∫ z in U, g z) - ∫ z in D, g z := by
  classical
  have h := integral_piecewise (μ := volume.restrict U) hD
    (hf.restrict (t := U)) (hg.integrableOn (s := Dᶜ))
  rw [Measure.restrict_restrict_of_subset hDU, Measure.restrict_restrict hD.compl,
    inter_comm Dᶜ U, ← Set.sdiff_eq U D, setIntegral_sdiff hD hg hDU] at h
  rw [h]
  ring

end PoincareConjecture.M65Interior

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior

theorem exists_disk_replacement {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (x : LoopPlane) (r : ℝ)
    (hDU : closedBall x r ⊆ U) (q : LoopPlane → M)
    (d : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (hq : MemLp (fun z => e (q z)) 2 (volume.restrict (closedBall x r)))
    (hd : ∀ i, MemLp (d i) 2 (volume.restrict (closedBall x r)))
    (hgreen : ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
      (∫ z in closedBall x r,
        test z * d i z j + fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (q z) j) =
      ∫ z in closedBall x r, test z * F.derivative i z j +
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (F.value z) j) :
    ∃ G : M65LocalWeakMap e U,
      (∀ z ∈ closedBall x r, G.value z = q z ∧ ∀ i, G.derivative i z = d i z) ∧
      ∀ z ∉ closedBall x r, G.value z = F.value z ∧
        ∀ i, G.derivative i z = F.derivative i z := by
  classical
  let D := closedBall x r
  have hD : MeasurableSet D := isClosed_closedBall.measurableSet
  let q' := D.piecewise q F.value
  let d' (i : Fin 2) := D.piecewise (d i) (F.derivative i)
  have hvalue (K : Set LoopPlane) (hc : IsCompact K) (hs : K ⊆ U) :
      MemLp (fun z => e (q' z)) 2 (volume.restrict K) := by
    have heq : (fun z => e (q' z)) = D.piecewise (fun z => e (q z))
        (fun z => e (F.value z)) := by
      funext z
      by_cases hz : z ∈ D <;> simp [q', hz]
    rw [heq]
    exact memLp_piecewise_local hD hq (F.value_memLp K hc hs)
  have hderivative (i : Fin 2) (K : Set LoopPlane) (hc : IsCompact K) (hs : K ⊆ U) :
      MemLp (d' i) 2 (volume.restrict K) :=
    memLp_piecewise_local hD (hd i) (F.derivative_memLp i K hc hs)
  have hweak (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test)
      (hs : tsupport test ⊆ U) (i : Fin 2) (j : Fin N) :
      (∫ z in U, test z * d' i z j) =
        -(∫ z in U,
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (q' z) j) := by
    let dt := ∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test
    have hnD : IntegrableOn (fun z => test z * d i z j) D :=
      ((test.memLp 2 volume).restrict D).integrable_mul ((hd i).eval_piLp j)
    have hnV : IntegrableOn (fun z =>
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (q z) j) D :=
      ((dt.memLp 2 volume).restrict D).integrable_mul (hq.eval_piLp j)
    have hoD := F.test_derivative_integrable test hc hs i j
    have hoV := F.test_value_integrable test hc hs i j
    have heqD : (fun z => test z * d' i z j) =
        D.piecewise (fun z => test z * d i z j)
          (fun z => test z * F.derivative i z j) := by
      funext z
      by_cases hz : z ∈ D <;> simp [d', hz]
    have heqV : (fun z =>
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (q' z) j) =
        D.piecewise
          (fun z => fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (q z) j)
          (fun z => fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) *
            e (F.value z) j) := by
      funext z
      by_cases hz : z ∈ D <;> simp [q', hz]
    rw [heqD, heqV, integral_piecewise_correction hD hDU hnD hoD,
      integral_piecewise_correction hD hDU hnV hoV]
    have hmatch := hgreen test i j
    rw [integral_add hnD hnV, integral_add (hoD.mono_set hDU) (hoV.mono_set hDU)] at hmatch
    have hold := F.weak_derivative test hc hs i j
    linarith
  let G : M65LocalWeakMap e U :=
    { value := q'
      derivative := d'
      value_memLp := hvalue
      derivative_memLp := hderivative
      weak_derivative := hweak }
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    exact ⟨by simp [G, q', D, hz], fun i => by simp [G, d', D, hz]⟩
  · intro z hz
    exact ⟨by simp [G, q', D, hz], fun i => by simp [G, d', D, hz]⟩

end PoincareConjecture.M65LocalWeakMap
