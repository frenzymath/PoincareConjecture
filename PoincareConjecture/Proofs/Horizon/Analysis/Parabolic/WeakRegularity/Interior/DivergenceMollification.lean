




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Mollification
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy









open Set Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

private theorem spatial_sum {f : Fin n → Spacetime n → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (i : Fin n) (z : Spacetime n) :
    spatialDeriv i (fun y => ∑ j, f j y) z = ∑ j, spatialDeriv i (f j) z := by
  simp only [spatialDeriv, fderiv_fun_sum
    (fun j _ => (hf j).differentiable (by simp) z), ContinuousLinearMap.sum_apply]

private theorem spatial_mul {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) (z : Spacetime n) :
    spatialDeriv i (fun y => f y * g y) z =
      spatialDeriv i f z * g z + f z * spatialDeriv i g z := by
  dsimp only [spatialDeriv]
  rw [fderiv_fun_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem spatial_sub {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) (z : Spacetime n) :
    spatialDeriv i (fun y => f y - g y) z = spatialDeriv i f z - spatialDeriv i g z := by
  dsimp only [spatialDeriv]
  rw [fderiv_fun_sub (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  rfl

private theorem spatial_add {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) (z : Spacetime n) :
    spatialDeriv i (fun y => f y + g y) z = spatialDeriv i f z + spatialDeriv i g z := by
  dsimp only [spatialDeriv]
  rw [fderiv_fun_add (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  rfl

private theorem spatial_second_mul {q φ : Spacetime n → ℝ}
    (hq : ContDiff ℝ ∞ q) (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin n) (y : Spacetime n) :
    spatialDeriv j (spatialDeriv i (fun w => q w * φ w)) y =
      spatialDeriv j (spatialDeriv i q) y * φ y +
      spatialDeriv i q y * spatialDeriv j φ y +
      spatialDeriv j q y * spatialDeriv i φ y +
      q y * spatialDeriv j (spatialDeriv i φ) y := by
  have he : spatialDeriv i (fun w => q w * φ w) =
      fun w => spatialDeriv i q w * φ w + q w * spatialDeriv i φ w := by
    funext w
    exact spatial_mul hq hφ i w
  rw [he, spatial_add ((contDiff_spatialDeriv hq i).mul hφ)
    (hq.mul (contDiff_spatialDeriv hφ i)),
    spatial_mul (contDiff_spatialDeriv hq i) hφ,
    spatial_mul hq (contDiff_spatialDeriv hφ i)]
  ring

private theorem derivative_translate {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (z y v : Spacetime n) :
    fderiv ℝ (translatedKernel η z) y v = -fderiv ℝ η (z - y) v := by
  have hd := (hη.differentiable (by simp) (z - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
  change HasFDerivAt (translatedKernel η z) _ y at hd
  rw [hd.fderiv]
  simp

private theorem second_translate {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (i j : Fin n) (z y : Spacetime n) :
    spatialDeriv j (spatialDeriv i (translatedKernel η z)) y =
      spatialDeriv j (spatialDeriv i η) (z - y) := by
  have he : spatialDeriv i (translatedKernel η z) =
      fun w => -translatedKernel (spatialDeriv i η) z w := by
    funext w
    exact derivative_translate hη z w (spatialDirection i)
  rw [he]
  change fderiv ℝ (-(translatedKernel (spatialDeriv i η) z)) y (spatialDirection j) = _
  rw [fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply,
    derivative_translate (contDiff_spatialDeriv hη i), neg_neg, spatialDeriv]

private theorem convolution_spatial {η f : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hf : Continuous f)
    (i : Fin n) (z : Spacetime n) :
    spatialDeriv i (lebesgueConvolution η f) z =
      lebesgueConvolution (spatialDeriv i η) f z :=
  fderiv_lebesgueConvolution hf.locallyIntegrable hη hηc z (spatialDirection i)

private theorem convolution_time {η f : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hf : Continuous f)
    (z : Spacetime n) :
    timeDeriv (lebesgueConvolution η f) z = lebesgueConvolution (timeDeriv η) f z :=
  fderiv_lebesgueConvolution hf.locallyIntegrable hη hηc z (0, 1)

private theorem integrable_translated_product {η f : Spacetime n → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) (hf : Continuous f)
    (z : Spacetime n) : Integrable (fun y => η (z - y) * f y) :=
  ((hη.comp (continuous_const.sub continuous_id)).mul hf).integrable_of_hasCompactSupport
    ((hηc.comp_homeomorph (Homeomorph.subLeft z)).mul_right)









theorem divergence_form_operator_identity
    {C : Coefficients n} {u : Spacetime n → ℝ}
    (hCprincipal : ∀ i j, ContDiff ℝ ∞ (C.principal i j))
    (hu : ContDiff ℝ ∞ u) (z : Spacetime n) :
    timeDeriv u z -
        ∑ i, spatialDeriv i
          (fun y => ∑ j, C.principal i j y * spatialDeriv j u y) z =
      C.operator u z -
        ((∑ i, C.drift i z * spatialDeriv i u z) +
          ∑ i, (∑ j, spatialDeriv j (C.principal j i) z) *
            spatialDeriv i u z) - C.zeroth z * u z := by
  have hprod (i j : Fin n) (y : Spacetime n) :
      spatialDeriv i
          (fun w => C.principal i j w * spatialDeriv j u w) y =
        spatialDeriv i (C.principal i j) y * spatialDeriv j u y +
          C.principal i j y * spatialDeriv i (spatialDeriv j u) y := by
    exact spatial_mul (hCprincipal i j) (contDiff_spatialDeriv hu j) i y
  have hsum (i : Fin n) :
      spatialDeriv i
          (fun y => ∑ j, C.principal i j y * spatialDeriv j u y) z =
        ∑ j, (spatialDeriv i (C.principal i j) z * spatialDeriv j u z +
          C.principal i j z * spatialDeriv i (spatialDeriv j u) z) := by
    rw [spatial_sum (fun j => (hCprincipal i j).mul (contDiff_spatialDeriv hu j)) i z]
    exact Finset.sum_congr rfl (fun j _ => hprod i j z)
  simp only [Coefficients.operator]
  rw [show (∑ i, spatialDeriv i
      (fun y => ∑ j, C.principal i j y * spatialDeriv j u y) z) =
      ∑ i, ∑ j, (spatialDeriv i (C.principal i j) z * spatialDeriv j u z +
        C.principal i j z * spatialDeriv i (spatialDeriv j u) z) by
        exact Finset.sum_congr rfl (fun i _ => hsum i)]
  simp only [Finset.sum_add_distrib]
  have hrename : (∑ i, ∑ j, spatialDeriv i (C.principal i j) z *
      spatialDeriv j u z) =
      ∑ i, (∑ j, spatialDeriv j (C.principal j i) z) * spatialDeriv i u z := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [hrename]
  let A : ℝ := ∑ x, ∑ y, C.principal x y z *
    spatialDeriv x (spatialDeriv y u) z
  let D : ℝ := ∑ x, (∑ y, spatialDeriv y (C.principal y x) z) *
    spatialDeriv x u z
  let B : ℝ := ∑ x, C.drift x z * spatialDeriv x u z
  change timeDeriv u z - (D + A) =
    timeDeriv u z - A + B + C.zeroth z * u z - (B + D) - C.zeroth z * u z
  ring




theorem spatial_deriv_coefficient_mollification
    {q u η : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hu : Continuous u)
    (i j : Fin n) (z : Spacetime n) :
    spatialDeriv i (fun y => q y * spatialDeriv j
      (lebesgueConvolution η u) y) z =
      spatialDeriv i q z * lebesgueConvolution (spatialDeriv j η) u z +
        q z * lebesgueConvolution (spatialDeriv i (spatialDeriv j η)) u z := by
  rw [spatial_mul hq
    (contDiff_spatialDeriv
      (contDiff_lebesgueConvolution hu.locallyIntegrable hη hηc) j) i z]
  rw [convolution_spatial hη hηc hu j z]
  have hj : spatialDeriv j (lebesgueConvolution η u) =
      lebesgueConvolution (spatialDeriv j η) u := by
    funext y
    exact convolution_spatial hη hηc hu j y
  rw [hj]
  have hi := convolution_spatial (contDiff_spatialDeriv hη j)
    (hηc.fderiv_apply ℝ (spatialDirection j)) hu i z
  rw [hi]

theorem spatial_deriv_mollified_product
    {q u η : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hu : Continuous u)
    (i : Fin n) (z : Spacetime n) :
    spatialDeriv i (lebesgueConvolution η (fun y => q y * u y)) z =
      lebesgueConvolution (spatialDeriv i η) (fun y => q y * u y) z := by
  exact convolution_spatial hη hηc (hq.continuous.mul hu) i z

theorem translated_integral_add
    {η f g : Spacetime n → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) (hf : Continuous f) (hg : Continuous g)
    (z : Spacetime n) :
    (∫ y, η (z - y) * (f y + g y)) =
      (∫ y, η (z - y) * f y) + ∫ y, η (z - y) * g y := by
  have hfi := integrable_translated_product hη hηc hf z
  have hgi := integrable_translated_product hη hηc hg z
  have heq : (fun y => η (z - y) * (f y + g y)) =
      (fun y => η (z - y) * f y + η (z - y) * g y) := by
    funext y
    ring
  rw [heq, integral_add hfi hgi]

theorem translated_integral_finsetSum
    {η : Spacetime n → ℝ} {f : Fin n → Spacetime n → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hf : ∀ i, Continuous (f i)) (z : Spacetime n) :
    (∫ y, η (z - y) * (∑ i, f i y)) =
      ∑ i, ∫ y, η (z - y) * f i y := by
  have hi : ∀ i, Integrable (fun y => η (z - y) * f i y) :=
    fun i => integrable_translated_product hη hηc (hf i) z
  have heq : (fun y => η (z - y) * (∑ i, f i y)) =
      (fun y => ∑ i, η (z - y) * f i y) := by
    funext y
    rw [Finset.mul_sum]
  rw [heq, integral_finsetSum _ (fun i _ => hi i)]

theorem translated_integral_sub
    {η f g : Spacetime n → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) (hf : Continuous f) (hg : Continuous g)
    (z : Spacetime n) :
    (∫ y, η (z - y) * (f y - g y)) =
      (∫ y, η (z - y) * f y) - ∫ y, η (z - y) * g y := by
  have hfi := integrable_translated_product hη hηc hf z
  have hgi := integrable_translated_product hη hηc hg z
  have heq : (fun y => η (z - y) * (f y - g y)) =
      (fun y => η (z - y) * f y - η (z - y) * g y) := by
    funext y
    ring
  rw [heq, integral_sub hfi hgi]

theorem WeakSolutionOn.mollified_divergence_equation
    {C : Coefficients n} {u η : Spacetime n → ℝ} {U : Set (Spacetime n)}
    (hprincipal : ∀ i j, ContDiff ℝ ∞ (C.principal i j))
    (hdrift : ∀ i, ContDiff ℝ ∞ (C.drift i))
    (hzeroth : ContDiff ℝ ∞ C.zeroth) (hu : Continuous u)
    (hw : WeakSolutionOn C u U) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {z : Spacetime n}
    (hz : tsupport (translatedKernel η z) ⊆ U) :
    timeDeriv (lebesgueConvolution η u) z -
        ∑ i, spatialDeriv i
          (fun y => ∑ j, C.principal i j y *
            spatialDeriv j (lebesgueConvolution η u) y) z =
      lebesgueConvolution η
          (fun y => ((∑ i, spatialDeriv i
            (fun w => C.drift i w + ∑ j, spatialDeriv j (C.principal j i) w) y) -
            C.zeroth y) * u y) z +
        ∑ i, spatialDeriv i
          (fun y =>
            -∑ j, (C.principal i j y * spatialDeriv j (lebesgueConvolution η u) y -
              lebesgueConvolution (spatialDeriv j η)
                (fun w => C.principal i j w * u w) y +
              lebesgueConvolution η
                (fun w => spatialDeriv j (C.principal i j) w * u w) y) -
            lebesgueConvolution η
              (fun w => (C.drift i w + ∑ j, spatialDeriv j (C.principal j i) w) * u w) y) z := by
  let d : Fin n → Spacetime n → ℝ := fun i y =>
    C.drift i y + ∑ j, spatialDeriv j (C.principal j i) y
  have hd (i : Fin n) : ContDiff ℝ ∞ (d i) :=
    (hdrift i).add (ContDiff.sum (fun j _ => contDiff_spatialDeriv (hprincipal j i) j))
  let w := lebesgueConvolution η u
  have hwreg : ContDiff ℝ ∞ w := contDiff_lebesgueConvolution hu.locallyIntegrable hη hηc
  have hconv {k g : Spacetime n → ℝ} (hk : ContDiff ℝ ∞ k)
      (hkc : HasCompactSupport k) (hg : Continuous g) :
      ContDiff ℝ ∞ (lebesgueConvolution k g) :=
    contDiff_lebesgueConvolution hg.locallyIntegrable hk hkc
  let H : Spacetime n → ℝ := fun y => (∑ i, spatialDeriv i (d i) y) - C.zeroth y
  have hH : ContDiff ℝ ∞ H :=
    (ContDiff.sum (fun i _ => contDiff_spatialDeriv (hd i) i)).sub hzeroth
  let R : Spacetime n → ℝ := fun y =>
    η (z - y) * (H y * u y) + ∑ i,
      ((∑ j, (spatialDeriv i (spatialDeriv j η) (z - y) * (C.principal i j y * u y) -
        spatialDeriv i η (z - y) * (spatialDeriv j (C.principal i j) y * u y))) -
        spatialDeriv i η (z - y) * (d i y * u y))
  have hI {k g : Spacetime n → ℝ} (hk : ContDiff ℝ ∞ k)
      (hkc : HasCompactSupport k) (hg : Continuous g) :
      Integrable (fun y => k (z - y) * g y) :=
    integrable_translated_product hk.continuous hkc hg z
  have hI₂ (i j : Fin n) := hI
    (contDiff_spatialDeriv (contDiff_spatialDeriv hη j) i)
    ((hηc.fderiv_apply ℝ (spatialDirection j)).fderiv_apply ℝ (spatialDirection i))
    ((hprincipal i j).continuous.mul hu)
  have hI₁ (i j : Fin n) := hI (contDiff_spatialDeriv hη i)
    (hηc.fderiv_apply ℝ (spatialDirection i))
    ((contDiff_spatialDeriv (hprincipal i j) j).continuous.mul hu)
  have hId (i : Fin n) := hI (contDiff_spatialDeriv hη i)
    (hηc.fderiv_apply ℝ (spatialDirection i)) ((hd i).continuous.mul hu)
  have hIH := hI hη hηc (hH.continuous.mul hu)
  have hIR : Integrable R := hIH.add (integrable_finsetSum _ (fun i _ =>
    (integrable_finsetSum _ (fun j _ => (hI₂ i j).sub (hI₁ i j))).sub (hId i)))
  have hIt := hI (contDiff_timeDeriv hη) (hasCompactSupport_timeDeriv hηc) hu
  have hzero := hw.2 (translatedKernel η z)
    (hη.comp (contDiff_const.sub contDiff_id))
    (hηc.comp_homeomorph (Homeomorph.subLeft z)) hz
  have hpoint (y : Spacetime n) :
      timeDeriv η (z - y) * u y - R y = u y * C.adjoint (translatedKernel η z) y := by
    have hφ : ContDiff ℝ ∞ (translatedKernel η z) :=
      hη.comp (contDiff_const.sub contDiff_id)
    have hdd (i : Fin n) : spatialDeriv i (d i) y =
        spatialDeriv i (C.drift i) y +
          ∑ j, spatialDeriv i (spatialDeriv j (C.principal j i)) y := by
      rw [show d i = fun x => C.drift i x + ∑ j, spatialDeriv j (C.principal j i) x by rfl,
        spatial_add (hdrift i) (ContDiff.sum (fun j _ => contDiff_spatialDeriv (hprincipal j i) j)),
        spatial_sum (fun j => contDiff_spatialDeriv (hprincipal j i) j)]
    have htrans (i : Fin n) : spatialDeriv i (translatedKernel η z) y =
        -spatialDeriv i η (z-y) := derivative_translate hη z y (spatialDirection i)
    have htransT : timeDeriv (translatedKernel η z) y = -timeDeriv η (z-y) :=
      derivative_translate hη z y (0, 1)
    have hpa (i j : Fin n) := spatial_second_mul (hprincipal i j) hφ i j y
    have hpb (i : Fin n) := spatial_mul (hdrift i) hφ i y
    simp only [Coefficients.adjoint]
    simp_rw [hpa, hpb]
    simp only [htrans, htransT, second_translate hη, translatedKernel, neg_neg]
    dsimp only [R, H]
    simp only [hdd, d, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_add, mul_sub, add_mul, sub_mul, Finset.mul_sum, Finset.sum_mul, mul_neg]
    have hs₁ : (∑ i, ∑ j, η (z-y) *
        (spatialDeriv i (spatialDeriv j (C.principal j i)) y * u y)) =
        ∑ i, ∑ j, η (z-y) *
          (spatialDeriv j (spatialDeriv i (C.principal i j)) y * u y) :=
      Finset.sum_comm
    have hs₂ : (∑ i, ∑ j, spatialDeriv i η (z-y) *
        (spatialDeriv j (C.principal j i) y * u y)) =
        ∑ i, ∑ j, spatialDeriv j η (z-y) *
          (spatialDeriv i (C.principal i j) y * u y) := Finset.sum_comm
    have hs₃ : (∑ i, ∑ j, u y *
        (C.principal i j y * spatialDeriv j (spatialDeriv i η) (z-y))) =
        ∑ i, ∑ j, spatialDeriv i (spatialDeriv j η) (z-y) *
          (C.principal i j y * u y) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [spatialSecond_comm η hη j i]
      ring
    rw [hs₁, hs₂, hs₃]
    simp only [Finset.sum_neg_distrib, mul_comm, mul_left_comm, mul_assoc]
    ring
  have htime : timeDeriv w z = ∫ y, R y := by
    have he := integral_congr_ae (μ := volume) (Eventually.of_forall hpoint)
    rw [integral_sub hIt hIR, hzero] at he
    rw [convolution_time hη hηc hu]
    change (∫ y, timeDeriv η (z - y) * u y) = _
    linarith
  have hR : (∫ y, R y) = lebesgueConvolution η (fun y => H y * u y) z +
      ∑ i, ((∑ j, (lebesgueConvolution (spatialDeriv i (spatialDeriv j η))
          (fun y => C.principal i j y * u y) z -
        lebesgueConvolution (spatialDeriv i η)
          (fun y => spatialDeriv j (C.principal i j) y * u y) z)) -
        lebesgueConvolution (spatialDeriv i η) (fun y => d i y * u y) z) := by
    dsimp only [R]
    erw [integral_add hIH (integrable_finsetSum Finset.univ (fun i _ =>
        (integrable_finsetSum Finset.univ (fun j _ => (hI₂ i j).sub (hI₁ i j))).sub (hId i))),
      integral_finsetSum Finset.univ (fun i _ =>
        (integrable_finsetSum Finset.univ (fun j _ => (hI₂ i j).sub (hI₁ i j))).sub (hId i))]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    erw [integral_sub (integrable_finsetSum Finset.univ (fun j _ => (hI₂ i j).sub (hI₁ i j))) (hId i),
      integral_finsetSum Finset.univ (fun j _ => (hI₂ i j).sub (hI₁ i j))]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_sub (hI₂ i j) (hI₁ i j)
  rw [hR] at htime
  let Q : Fin n → Fin n → Spacetime n → ℝ := fun i j y =>
    C.principal i j y * spatialDeriv j w y -
      lebesgueConvolution (spatialDeriv j η) (fun x => C.principal i j x * u x) y +
      lebesgueConvolution η (fun x => spatialDeriv j (C.principal i j) x * u x) y
  have hQ (i j : Fin n) : ContDiff ℝ ∞ (Q i j) :=
    (((hprincipal i j).mul (contDiff_spatialDeriv hwreg j)).sub
      (hconv (contDiff_spatialDeriv hη j) (hasCompactSupport_spatialDeriv j hηc)
        ((hprincipal i j).continuous.mul hu))).add
      (hconv hη hηc ((contDiff_spatialDeriv (hprincipal i j) j).continuous.mul hu))
  have hQd (i j : Fin n) : spatialDeriv i (Q i j) z =
      spatialDeriv i (fun y => C.principal i j y * spatialDeriv j w y) z -
        lebesgueConvolution (spatialDeriv i (spatialDeriv j η))
          (fun y => C.principal i j y * u y) z +
        lebesgueConvolution (spatialDeriv i η)
          (fun y => spatialDeriv j (C.principal i j) y * u y) z := by
    dsimp only [Q]
    erw [spatial_add
      (((hprincipal i j).mul (contDiff_spatialDeriv hwreg j)).sub
        (hconv (contDiff_spatialDeriv hη j) (hasCompactSupport_spatialDeriv j hηc)
          ((hprincipal i j).continuous.mul hu)))
      (hconv hη hηc ((contDiff_spatialDeriv (hprincipal i j) j).continuous.mul hu)),
      spatial_sub ((hprincipal i j).mul (contDiff_spatialDeriv hwreg j))
        (hconv (contDiff_spatialDeriv hη j) (hasCompactSupport_spatialDeriv j hηc)
          ((hprincipal i j).continuous.mul hu)),
      convolution_spatial (contDiff_spatialDeriv hη j) (hasCompactSupport_spatialDeriv j hηc)
        ((hprincipal i j).continuous.mul hu),
      convolution_spatial hη hηc ((contDiff_spatialDeriv (hprincipal i j) j).continuous.mul hu)]
    rfl
  have hF (i : Fin n) : spatialDeriv i
      (fun y => -(∑ j, Q i j y) - lebesgueConvolution η (fun x => d i x * u x) y) z =
      -(∑ j, spatialDeriv i (Q i j) z) -
        lebesgueConvolution (spatialDeriv i η) (fun y => d i y * u y) z := by
    erw [spatial_sub (ContDiff.sum (s := Finset.univ) (fun j _ => hQ i j)).neg
      (hconv hη hηc ((hd i).continuous.mul hu))]
    have hn : spatialDeriv i (fun y => -(∑ j, Q i j y)) z =
        -spatialDeriv i (fun y => ∑ j, Q i j y) z := by
      change fderiv ℝ (-(fun y => ∑ j, Q i j y)) z (spatialDirection i) = _
      rw [fderiv_neg]
      rfl
    rw [hn, spatial_sum (fun j => hQ i j), convolution_spatial hη hηc ((hd i).continuous.mul hu)]
    rfl
  change timeDeriv w z -
      (∑ i, spatialDeriv i (fun y => ∑ j, C.principal i j y * spatialDeriv j w y) z) =
    lebesgueConvolution η (fun y => H y * u y) z +
      ∑ i, spatialDeriv i
        (fun y => -(∑ j, Q i j y) - lebesgueConvolution η (fun x => d i x * u x) y) z
  simp_rw [hF, hQd, spatial_sum (fun j => (hprincipal _ j).mul (contDiff_spatialDeriv hwreg j))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at htime ⊢
  linarith

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
