import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalization











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Euler

private theorem cutoff_graph {N : ℕ} {U : Set LoopPlane}
    (Y : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) U)
    (θ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ U) :
    MemLp (fun z => θ z • Y.value z) 2 volume ∧
      (∀ i, MemLp (fun z => θ z • Y.derivative i z +
        fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • Y.value z) 2 volume) ∧
      ∀ (φ : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
        (∫ z, φ z * (θ z • Y.derivative i z +
          fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • Y.value z) j) =
        -(∫ z, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) *
          (θ z • Y.value z) j) := by
  choose u d hu hd hw using fun j => Y.cutoff_global j θ hc hs
  refine ⟨MemLp.of_eval_piLp (fun j => (Lp.memLp (u j)).ae_eq (hu j)),
    fun i => MemLp.of_eval_piLp (fun j => (Lp.memLp (d j i)).ae_eq (hd j i)), ?_⟩
  intro φ i j
  have h := hw j i φ
  rw [DeTurckDomainRegularityNative.inner_schwartz] at h
  have hleft : (∫ z, d j i z * φ z) =
      ∫ z, φ z * (θ z • Y.derivative i z +
        fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • Y.value z) j := by
    apply integral_congr_ae
    filter_upwards [hd j i] with z hz
    rw [hz]
    exact mul_comm _ _
  have hright : (∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      ∫ z, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (θ z • Y.value z) j := by
    apply integral_congr_ae
    filter_upwards [hu j] with z hz
    rw [hz]
    exact mul_comm _ _
  rwa [hleft, hright] at h

set_option maxHeartbeats 800000 in





def compact_variation {N : ℕ} {U : Set LoopPlane}
    (X Y : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) U)
    (θ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ U)
    (t : ℝ) : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) U := by
  let W (z : LoopPlane) := θ z • Y.value z
  let A (i : Fin 2) (z : LoopPlane) := θ z • Y.derivative i z +
    fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • Y.value z
  have hW := (cutoff_graph Y θ hc hs).1
  have hA := (cutoff_graph Y θ hc hs).2.1
  have hw := (cutoff_graph Y θ hc hs).2.2
  have hzero (z : LoopPlane) (hz : z ∉ U) : W z = 0 ∧ ∀ i, A i z = 0 := by
    have hzθ : z ∉ tsupport θ := fun hm => hz (hs hm)
    have hθ := image_eq_zero_of_notMem_tsupport hzθ
    have hD := fderiv_of_notMem_tsupport ℝ hzθ
    exact ⟨by simp only [W, hθ, zero_smul], fun i => by
      simp only [A, hθ, hD, zero_apply, zero_smul, add_zero]⟩
  refine {
    value := fun z => X.value z + t • W z
    derivative := fun i z => X.derivative i z + t • A i z
    value_memLp := fun K hK hKU => (X.value_memLp K hK hKU).add ((hW.restrict K).const_smul t)
    derivative_memLp := fun i K hK hKU =>
      (X.derivative_memLp i K hK hKU).add (((hA i).restrict K).const_smul t)
    weak_derivative := ?_ }
  intro φ hφ hφU i j
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hXA := X.test_derivative_integrable φ hφ hφU i j
  have hXV := X.test_value_integrable φ hφ hφU i j
  have hPA : IntegrableOn (fun z => φ z * A i z j) U :=
    ((φ.memLp 2 volume).integrable_mul ((hA i).eval_piLp j)).integrableOn
  have hPV : IntegrableOn (fun z => fderiv ℝ φ z b * W z j) U :=
    (((∂_{b} φ).memLp 2 volume).integrable_mul (hW.eval_piLp j)).integrableOn
  have hprod : (∫ z in U, φ z * A i z j) = -(∫ z in U, fderiv ℝ φ z b * W z j) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [(hzero z hz).2 i]; simp only [PiLp.zero_apply, mul_zero])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [(hzero z hz).1]; simp only [PiLp.zero_apply, mul_zero])]
    exact hw φ i j
  have hleft : (∫ z in U, φ z * (X.derivative i z + t • A i z) j) =
      (∫ z in U, φ z * X.derivative i z j) + t * ∫ z in U, φ z * A i z j := by
    calc
      _ = ∫ z in U, φ z * X.derivative i z j + t * (φ z * A i z j) := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by change φ z * (X.derivative i z j + t * A i z j) = _; ring
      _ = _ := by rw [integral_add hXA (hPA.const_mul t), integral_const_mul]
  have hright : (∫ z in U, fderiv ℝ φ z b * (X.value z + t • W z) j) =
      (∫ z in U, fderiv ℝ φ z b * X.value z j) +
        t * ∫ z in U, fderiv ℝ φ z b * W z j := by
    calc
      _ = ∫ z in U, fderiv ℝ φ z b * X.value z j + t * (fderiv ℝ φ z b * W z j) := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by change fderiv ℝ φ z b * (X.value z j + t * W z j) = _; ring
      _ = _ := by rw [integral_add hXV (hPV.const_mul t), integral_const_mul]
  change (∫ z in U, φ z * (X.derivative i z + t • A i z) j) =
    -(∫ z in U, fderiv ℝ φ z b * (X.value z + t • W z) j)
  rw [hleft, hright, X.weak_derivative φ hφ hφU i j, hprod]
  ring





theorem compact_variation_off_tsupport {N : ℕ} {U : Set LoopPlane}
    (X Y : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) U)
    (θ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ U)
    (t : ℝ) {z : LoopPlane} (hz : z ∉ tsupport θ) :
    (compact_variation X Y θ hc hs t).value z = X.value z ∧
      ∀ i, (compact_variation X Y θ hc hs t).derivative i z = X.derivative i z := by
  have hθ := image_eq_zero_of_notMem_tsupport hz
  have hD := fderiv_of_notMem_tsupport ℝ hz
  constructor
  · change X.value z + t • (θ z • Y.value z) = X.value z
    simp only [hθ, zero_smul, smul_zero, add_zero]
  · intro i
    change X.derivative i z + t • (θ z • Y.derivative i z +
      fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • Y.value z) = X.derivative i z
    simp only [hθ, hD, zero_apply, zero_smul, add_zero, smul_zero]

end PoincareConjecture.M65Euler
