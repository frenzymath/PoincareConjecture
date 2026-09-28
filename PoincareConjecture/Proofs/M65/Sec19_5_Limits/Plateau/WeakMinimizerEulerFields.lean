import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerLocal
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology SchwartzMap ContDiff LineDeriv

universe u v

namespace PoincareConjecture.M65Euler




def restrict_map {M : Type u} {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    {S T : Set LoopPlane} (F : M65LocalWeakMap e S) (hTS : T ⊆ S) :
    M65LocalWeakMap e T where
  value := F.value
  derivative := F.derivative
  value_memLp K hK hKT := F.value_memLp K hK (hKT.trans hTS)
  derivative_memLp i K hK hKT := F.derivative_memLp i K hK (hKT.trans hTS)
  weak_derivative φ hc hs i j := by
    let b := EuclideanSpace.basisFun (Fin 2) ℝ i
    have hleft (V : Set LoopPlane) (hV : tsupport φ ⊆ V) :
        (∫ z in V, φ z * F.derivative i z j) = ∫ z, φ z * F.derivative i z j :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hV hm)), zero_mul])
    have hright (V : Set LoopPlane) (hV : tsupport φ ⊆ V) :
        (∫ z in V, fderiv ℝ φ z b * e (F.value z) j) =
          ∫ z, fderiv ℝ φ z b * e (F.value z) j :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hm => hz (hV hm)), zero_apply, zero_mul])
    have hw := F.weak_derivative φ hc (hs.trans hTS) i j
    rw [hleft S (hs.trans hTS), hright S (hs.trans hTS)] at hw
    rw [hleft T hs, hright T hs]
    exact hw




def replace_value {M : Type u} {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    {S : Set LoopPlane} (F : M65LocalWeakMap e S) (q : LoopPlane → M)
    (hq : (fun z => e (q z)) =ᵐ[volume.restrict S] fun z => e (F.value z)) :
    M65LocalWeakMap e S where
  value := q
  derivative := F.derivative
  value_memLp K hK hKS := (F.value_memLp K hK hKS).ae_eq
    (ae_restrict_of_ae_restrict_of_subset hKS hq.symm)
  derivative_memLp := F.derivative_memLp
  weak_derivative φ hc hs i j := by
    rw [F.weak_derivative φ hc hs i j]
    congr 1
    apply integral_congr_ae
    filter_upwards [hq] with z hz
    rw [hz]





theorem derivative_unique {M : Type u} {M' : Type v} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {e' : M' → EuclideanSpace ℝ (Fin N)}
    {S : Set LoopPlane} (hS : IsOpen S) (F : M65LocalWeakMap e S)
    (G : M65LocalWeakMap e' S)
    (heq : (fun z => e (F.value z)) =ᵐ[volume.restrict S]
      fun z => e' (G.value z)) (i : Fin 2) :
    F.derivative i =ᵐ[volume.restrict S] G.derivative i := by
  have hlocF (j : Fin N) : LocallyIntegrableOn (fun z => F.derivative i z j) S volume := by
    apply (locallyIntegrableOn_iff hS.isLocallyClosed).mpr
    intro K hKS hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact ((F.derivative_memLp i K hK hKS).eval_piLp j).integrable (by norm_num)
  have hlocG (j : Fin N) : LocallyIntegrableOn (fun z => G.derivative i z j) S volume := by
    apply (locallyIntegrableOn_iff hS.isLocallyClosed).mpr
    intro K hKS hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact ((G.derivative_memLp i K hK hKS).eval_piLp j).integrable (by norm_num)
  have hj (j : Fin N) : ∀ᵐ z ∂volume, z ∈ S →
      F.derivative i z j - G.derivative i z j = 0 := by
    apply hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hlocF j).sub (hlocG j))
    intro ψ hψ hc hs
    let φ : 𝓢(LoopPlane, ℝ) := hc.toSchwartzMap hψ
    have hwF := F.weak_derivative φ hc hs i j
    have hwG := G.weak_derivative φ hc hs i j
    have hright : (∫ z in S, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) *
        e (F.value z) j) =
      ∫ z in S, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e' (G.value z) j := by
      apply integral_congr_ae
      filter_upwards [heq] with z hz
      rw [hz]
    have hleft : (∫ z in S, φ z * F.derivative i z j) =
        ∫ z in S, φ z * G.derivative i z j := by rw [hwF, hwG, hright]
    calc
      _ = ∫ z in S, φ z * F.derivative i z j - φ z * G.derivative i z j := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
          rw [show φ z = 0 from image_eq_zero_of_notMem_tsupport (fun hm => hz (hs hm))]
          simp only [zero_mul, sub_self])]
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          change ψ z * (F.derivative i z j - G.derivative i z j) =
            ψ z * F.derivative i z j - ψ z * G.derivative i z j
          ring
      _ = 0 := by
        rw [integral_sub (F.test_derivative_integrable φ hc hs i j)
          (G.test_derivative_integrable φ hc hs i j), hleft, sub_self]
  filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hj), ae_restrict_mem hS.measurableSet]
    with z hz hzs
  ext j
  exact sub_eq_zero.mp (hz j hzs)

end PoincareConjecture.M65Euler
