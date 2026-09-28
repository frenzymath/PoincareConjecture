import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerStationarity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

namespace PoincareConjecture.M65Euler

theorem vector_firstVariation_eq_sum {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (A : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (φ : 𝓢(LoopPlane, EuclideanSpace ℝ (Fin N))) (z : LoopPlane) :
    (∑ i : Fin 2, fderiv ℝ g.euclideanCoefficients (X z) (φ z) (A i z) (A i z)) +
        2 * ∑ i : Fin 2, g.euclideanCoefficients (X z) (A i z)
          (fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      2 * ∑ k : Fin N, firstVariationDensity g X A
        (fun _ => EuclideanSpace.basisFun (Fin N) ℝ k)
        (φ.postcompCLM (EuclideanSpace.proj k)) z := by
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have hD (k : Fin N) (v : LoopPlane) :
      fderiv ℝ (φ.postcompCLM (EuclideanSpace.proj k)) z v = (fderiv ℝ φ z v) k := by
    have hh := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp z
      φ.differentiableAt.hasFDerivAt
    exact congrArg (fun L => L v) hh.fderiv
  have hmetric (i : Fin 2) :
      (∑ k : Fin N, fderiv ℝ g.euclideanCoefficients (X z) (φ z k • b k)
        (A i z) (A i z)) =
        fderiv ℝ g.euclideanCoefficients (X z) (φ z) (A i z) (A i z) := by
    simpa only [b, EuclideanSpace.basisFun_repr, map_sum, sum_apply]
      using congrArg (fun v => fderiv ℝ g.euclideanCoefficients (X z) v (A i z) (A i z))
        (b.sum_repr (φ z))
  have hcolumn (i : Fin 2) :
      (∑ k : Fin N, g.euclideanCoefficients (X z)
        ((fderiv ℝ φ z (EuclideanSpace.single i 1)) k • b k) (A i z)) =
        g.euclideanCoefficients (X z) (A i z)
          (fderiv ℝ φ z (EuclideanSpace.single i 1)) := by
    have hh := congrArg (fun v => g.euclideanCoefficients (X z) v (A i z))
      (b.sum_repr (fderiv ℝ φ z (EuclideanSpace.single i 1)))
    have heq : (∑ k : Fin N, g.euclideanCoefficients (X z)
        ((fderiv ℝ φ z (EuclideanSpace.single i 1)) k • b k) (A i z)) =
        g.euclideanCoefficients (X z)
          (fderiv ℝ φ z (EuclideanSpace.single i 1)) (A i z) := by
      simpa only [b, EuclideanSpace.basisFun_repr, map_sum, sum_apply] using hh
    exact heq.trans (g.symm (X z) _ _)
  symm
  calc
    _ = 2 * ∑ i : Fin 2,
        ((1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (X z) (φ z) (A i z) (A i z) +
          g.euclideanCoefficients (X z) (A i z)
            (fderiv ℝ φ z (EuclideanSpace.single i 1))) := by
      congr 1
      unfold firstVariationDensity
      simp only [SchwartzMap.postcompCLM_apply, fderiv_const_apply, zero_apply,
        smul_zero, zero_add, EuclideanSpace.basisFun_apply, hD]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simpa +instances only [b, EuclideanSpace.basisFun_apply] using!
        congrArg₂ (fun a c : ℝ => (1 / 2 : ℝ) * a + c) (hmetric i) (hcolumn i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

theorem vector_firstVariation_eq_zero_of_notMem_tsupport {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (A : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (φ : 𝓢(LoopPlane, EuclideanSpace ℝ (Fin N))) {z : LoopPlane}
    (hz : z ∉ tsupport φ) :
    (∑ i : Fin 2, fderiv ℝ g.euclideanCoefficients (X z) (φ z) (A i z) (A i z)) +
        2 * ∑ i : Fin 2, g.euclideanCoefficients (X z) (A i z)
          (fderiv ℝ φ z (EuclideanSpace.single i 1)) = 0 := by
  rw [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]
  simp only [map_zero, zero_apply, Finset.sum_const_zero, mul_zero, add_zero]

set_option maxHeartbeats 1200000 in

theorem variational_vector_equation {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x (8 * R)))
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (hcmp : ∀ (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)), ContDiff ℝ 1 V →
      ∀ CV : NNReal, (∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ)) →
        ∀ (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ ball x R →
          ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
            (∫ z in closedBall x (2 * R), coordinateHalfEnergy g X.value X.derivative z) ≤
              ∫ z in closedBall x (2 * R), coordinateHalfEnergy g
                (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z)
    (φ : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball x R) :
    let density := fun z =>
      (∑ i : Fin 2, fderiv ℝ g.euclideanCoefficients (X.value z) (φ z)
        (X.derivative i z) (X.derivative i z)) +
        2 * ∑ i : Fin 2, g.euclideanCoefficients (X.value z) (X.derivative i z)
          (fderiv ℝ φ z (EuclideanSpace.single i 1))
    IntegrableOn density (ball x R) ∧ (∫ z in ball x R, density z) = 0 := by
  intro density
  let Φ : 𝓢(LoopPlane, EuclideanSpace ℝ (Fin N)) := hc.toSchwartzMap hφ
  let ψ (k : Fin N) := Φ.postcompCLM (EuclideanSpace.proj k)
  let V (k : Fin N) (_ : EuclideanSpace ℝ (Fin N)) := EuclideanSpace.basisFun (Fin N) ℝ k
  have hψs (k : Fin N) : tsupport (ψ k) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero (EuclideanSpace.proj k)) Φ
  have hψc (k : Fin N) : HasCompactSupport (ψ k) :=
    hc.of_isClosed_subset isClosed_closure (hψs k)
  have hV (k : Fin N) : ContDiff ℝ 1 (V k) := contDiff_const
  have hVD (k : Fin N) (y : EuclideanSpace ℝ (Fin N)) : ‖fderiv ℝ (V k) y‖ ≤ (0 : NNReal) := by
    simp only [V, fderiv_const_apply, norm_zero, NNReal.coe_zero, le_refl]
  have hscalar (k : Fin N) := integral_firstVariation_eq_zero g x hR X a hε hXcap
    (V k) (hV k) 0 (hVD k) (ψ k) (hψc k) ((hψs k).trans hs)
    (hcmp (V k) (hV k) 0 (hVD k) (ψ k) (hψc k) ((hψs k).trans hs))
  have heq : density = fun z =>
      2 * ∑ k : Fin N, firstVariationDensity g X.value X.derivative (V k) (ψ k) z := by
    funext z
    exact vector_firstVariation_eq_sum g X.value X.derivative Φ z
  have hI : IntegrableOn density (closedBall x (2 * R)) := by
    rw [heq]
    exact (integrable_finsetSum _ fun k _ => (hscalar k).1).const_mul 2
  have hzero : (∫ z in closedBall x (2 * R), density z) = 0 := by
    rw [heq, integral_const_mul, integral_finsetSum _ fun k _ => (hscalar k).1]
    simp only [(hscalar _).2, Finset.sum_const_zero, mul_zero]
  have houtside (z : LoopPlane) (hz : z ∉ ball x R) : density z = 0 :=
    vector_firstVariation_eq_zero_of_notMem_tsupport g X.value X.derivative Φ
      (fun hm => hz (hs hm))
  have hsub : ball x R ⊆ closedBall x (2 * R) :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
  refine ⟨hI.mono_set hsub, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => houtside z (fun hm => hz (hsub hm)))] at hzero
  exact hzero

end PoincareConjecture.M65Euler
