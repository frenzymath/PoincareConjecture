import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanCutoffNative
import PoincareConjecture.Proofs.M03.Existence.CoordinateEllipticityNative

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap ContDiff LineDeriv

noncomputable section

namespace PoincareConjecture.DeTurckGeneratorRegularityNative

open EuclideanTranslationNative EuclideanDerivativeNative DeTurckDomainRegularityNative

section FiniteEnergy

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def gradientSize (w : ι → H) : ℝ := Real.sqrt (∑ i, ‖w i‖ ^ 2)

theorem gradientSize_nonneg (w : ι → H) : 0 ≤ gradientSize w := Real.sqrt_nonneg _

theorem gradientSize_sq (w : ι → H) : gradientSize w ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem norm_le_gradientSize (w : ι → H) (i : ι) : ‖w i‖ ≤ gradientSize w := by
  apply (sq_le_sq₀ (norm_nonneg _) (gradientSize_nonneg w)).mp
  rw [gradientSize_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i)

theorem sum_norm_le_gradientSize (w : ι → H) :
    (∑ i, ‖w i‖) ≤ (Fintype.card ι : ℝ) * gradientSize w := by
  calc
    _ ≤ ∑ _i : ι, gradientSize w := Finset.sum_le_sum (fun i _ => norm_le_gradientSize w i)
    _ = _ := by simp

theorem abs_crossEnergy_le (v w : ι → H) (r : ι → ι → H) {B : ℝ}
    (hB : 0 ≤ B) (hr : ∀ i j, ‖r i j‖ ≤ B * ‖v i‖) :
    |∑ i, ∑ j, inner ℝ (r i j) (w j)| ≤
      (Fintype.card ι : ℝ) * B * (∑ i, ‖v i‖) * gradientSize w := by
  calc
    _ ≤ ∑ i, ∑ j, |inner ℝ (r i j) (w j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ _j : ι, B * ‖v i‖ * gradientSize w := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hr i j) (norm_le_gradientSize w j) (norm_nonneg _)
          (mul_nonneg hB (norm_nonneg _)))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem gradientSize_le_of_energy (w : ι → H) {ell C : ℝ}
    (hEll : 0 < ell) (hC : 0 ≤ C)
    (henergy : ell * gradientSize w ^ 2 ≤ C * gradientSize w) :
    gradientSize w ≤ C / ell := by
  by_cases hw : gradientSize w = 0
  · rw [hw]
    exact div_nonneg hC hEll.le
  · have hwpos : 0 < gradientSize w := lt_of_le_of_ne (gradientSize_nonneg w) (Ne.symm hw)
    apply (le_div_iff₀ hEll).mpr
    nlinarith

theorem norm_le_of_discrete_energy (v w : ι → H) (r : ι → ι → H)
    (G test : H) {ell B principal : ℝ} (hEll : 0 < ell) (hB : 0 ≤ B)
    (hprincipal : ell * gradientSize w ^ 2 ≤ principal)
    (hr : ∀ i j, ‖r i j‖ ≤ B * ‖v i‖)
    (htest : ‖test‖ ≤ gradientSize w)
    (heq : principal + (∑ i, ∑ j, inner ℝ (r i j) (w j)) = inner ℝ G test)
    (i : ι) :
    ‖w i‖ ≤ (‖G‖ + (Fintype.card ι : ℝ) * B * (∑ j, ‖v j‖)) / ell := by
  apply (norm_le_gradientSize w i).trans
  apply gradientSize_le_of_energy w hEll (by positivity)
  have hc := abs_crossEnergy_le v w r hB hr
  have hright : inner ℝ G test ≤ ‖G‖ * gradientSize w :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left htest (norm_nonneg _))
  have hcross := (neg_le_abs (∑ i, ∑ j, inner ℝ (r i j) (w j))).trans hc
  nlinarith

end FiniteEnergy

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def translateSchwartz (a : E) (f : 𝓢(E, ℝ)) : 𝓢(E, ℝ) :=
  SchwartzMap.compSubConstCLM ℝ (-a) f

@[simp] theorem translateSchwartz_apply (a : E) (f : 𝓢(E, ℝ)) (x : E) :
    translateSchwartz a f x = f (x + a) := by
  simp only [translateSchwartz, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

theorem translateSchwartz_toLp (a : E) (f : 𝓢(E, ℝ)) :
    (translateSchwartz a f).toLp 2 volume = translateLp a (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(translateSchwartz a f).coeFn_toLp 2 volume,
    translateLp_ae_eq a (f.toLp 2 volume),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)]
      with x hleft hright hf
  rw [hleft, hright, hf, translateSchwartz_apply]

theorem lineDeriv_translateSchwartz (a v : E) (f : 𝓢(E, ℝ)) :
    ∂_{v} (translateSchwartz a f) = translateSchwartz a (∂_{v} f) := by
  ext x
  have hfun : (translateSchwartz a f : E → ℝ) = fun y => f (y + a) := by
    funext y
    exact translateSchwartz_apply a f y
  have hd : HasFDerivAt (fun y : E => f (y + a)) (fderiv ℝ f (x + a)) x := by
    convert! (f.hasFDerivAt (x + a)).comp x ((hasFDerivAt_id x).add_const a) using 1
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun, hd.fderiv,
    translateSchwartz_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

def differenceQuotientSchwartz (f : 𝓢(E, ℝ)) (v : E) (h : ℝ) : 𝓢(E, ℝ) :=
  h⁻¹ • (translateSchwartz (h • v) f - f)

@[simp] theorem differenceQuotientSchwartz_apply (f : 𝓢(E, ℝ)) (v : E) (h : ℝ) (x : E) :
    differenceQuotientSchwartz f v h x = h⁻¹ * (f (x + h • v) - f x) := by
  simp only [differenceQuotientSchwartz, SchwartzMap.smul_apply, SchwartzMap.sub_apply,
    translateSchwartz_apply, smul_eq_mul]

theorem differenceQuotientSchwartz_toLp (f : 𝓢(E, ℝ)) (v : E) (h : ℝ) :
    (differenceQuotientSchwartz f v h).toLp 2 volume =
      differenceQuotient (f.toLp 2 volume) v h := by
  change SchwartzMap.toLpCLM ℝ ℝ 2 volume (h⁻¹ • (translateSchwartz (h • v) f - f)) = _
  rw [map_smul, map_sub]
  simp only [SchwartzMap.toLpCLM_apply, translateSchwartz_toLp, differenceQuotient]

theorem lineDeriv_differenceQuotientSchwartz (f : 𝓢(E, ℝ)) (v w : E) (h : ℝ) :
    ∂_{w} (differenceQuotientSchwartz f v h) = differenceQuotientSchwartz (∂_{w} f) v h := by
  simp only [differenceQuotientSchwartz, LineDeriv.lineDerivOp_smul,
    sub_eq_add_neg, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_neg,
    lineDeriv_translateSchwartz]

theorem differenceQuotient_ae_eq (u : ScalarL2 n) (v : E) (h : ℝ) :
    differenceQuotient u v h =ᵐ[volume] fun x => h⁻¹ * (u (x + h • v) - u x) := by
  filter_upwards [Lp.coeFn_smul h⁻¹ (translateLp (h • v) u - u),
    Lp.coeFn_sub (translateLp (h • v) u) u, translateLp_ae_eq (h • v) u]
      with x hsmul hsub htrans
  change (h⁻¹ • (translateLp (h • v) u - u)) x = _
  rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, htrans, smul_eq_mul]

theorem schwartzMultiplier_selfAdjoint (A : 𝓢(E, ℝ)) (u w : ScalarL2 n) :
    inner ℝ (schwartzMultiplier A u) w = inner ℝ u (schwartzMultiplier A w) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [schwartzMultiplier_coe A u, schwartzMultiplier_coe A w] with x hu hw
  rw [hu, hw]
  simp only [Real.inner_apply]
  ring

theorem norm_schwartzMultiplier_le (A : 𝓢(E, ℝ)) (u : ScalarL2 n) {B : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ B) : ‖schwartzMultiplier A u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [schwartzMultiplier_coe A u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

theorem differenceQuotient_schwartzMultiplier (A : 𝓢(E, ℝ)) (u : ScalarL2 n)
    (v : E) (h : ℝ) :
    differenceQuotient (schwartzMultiplier A u) v h =
      schwartzMultiplier (translateSchwartz (h • v) A) (differenceQuotient u v h) +
        schwartzMultiplier (differenceQuotientSchwartz A v h) u := by
  apply Lp.ext
  filter_upwards [differenceQuotient_ae_eq (schwartzMultiplier A u) v h,
    schwartzMultiplier_coe A u,
    (measurePreserving_add_right volume (h • v)).quasiMeasurePreserving.ae
      (schwartzMultiplier_coe A u),
    Lp.coeFn_add (schwartzMultiplier (translateSchwartz (h • v) A) (differenceQuotient u v h))
      (schwartzMultiplier (differenceQuotientSchwartz A v h) u),
    schwartzMultiplier_coe (translateSchwartz (h • v) A) (differenceQuotient u v h),
    schwartzMultiplier_coe (differenceQuotientSchwartz A v h) u,
    differenceQuotient_ae_eq u v h] with x hleft hu hushift hadd hfirst hsecond hquot
  rw [hleft, hu, hushift, hadd, Pi.add_apply, hfirst, hsecond, hquot,
    translateSchwartz_apply, differenceQuotientSchwartz_apply]
  ring

theorem norm_differenceQuotientSchwartz_apply_le (A : 𝓢(E, ℝ)) (v : E)
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ x, ‖fderiv ℝ A x‖ ≤ B) (h : ℝ) (x : E) :
    ‖differenceQuotientSchwartz A v h x‖ ≤ B * ‖v‖ := by
  by_cases hh : h = 0
  · simp only [hh, differenceQuotientSchwartz_apply, inv_zero, zero_mul, norm_zero]
    exact mul_nonneg hB (norm_nonneg _)
  have hd := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => A.differentiableAt) (fun y _ => hA y) (mem_univ x) (mem_univ (x + h • v))
  rw [differenceQuotientSchwartz_apply, norm_mul]
  calc
    _ ≤ ‖h⁻¹‖ * (B * ‖(x + h • v) - x‖) :=
      mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = B * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_inv, ← mul_assoc, mul_comm |h|⁻¹ B, mul_assoc B,
        ← mul_assoc |h|⁻¹ |h|, inv_mul_cancel₀ (abs_ne_zero.mpr hh), one_mul]

theorem norm_doubleQuotient_schwartz_le (f : 𝓢(E, ℝ)) (v : E) (h k : ℝ) :
    ‖differenceQuotient (differenceQuotient (f.toLp 2 volume) v h) v k‖ ≤
      ‖differenceQuotient ((∂_{v} f).toLp 2 volume) v h‖ := by
  let q := differenceQuotientSchwartz f v h
  have hD : MemLp (fun x => fderiv ℝ q x v) 2 volume := (∂_{v} q).memLp 2 volume
  have hbound := norm_differenceQuotient_toLp_le v (q.smooth 1)
    (q.memLp 2 volume) hD k
  change ‖differenceQuotient (q.toLp 2 volume) v k‖ ≤ ‖(∂_{v} q).toLp 2 volume‖ at hbound
  simpa only [q, differenceQuotientSchwartz_toLp, lineDeriv_differenceQuotientSchwartz] using hbound

theorem norm_doubleQuotient_le_of_denseRange {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (S : α → 𝓢(E, ℝ))
    (U D : β → ScalarL2 n) (hU : Continuous U) (hD : Continuous D) (v : E)
    (hSU : ∀ a, U (e a) = (S a).toLp 2 volume)
    (hSD : ∀ a, D (e a) = (∂_{v} (S a)).toLp 2 volume)
    (z : β) (h k : ℝ) :
    ‖differenceQuotient (differenceQuotient (U z) v h) v k‖ ≤
      ‖differenceQuotient (D z) v h‖ := by
  apply norm_differenceQuotient_le_of_denseRange e he
    (fun y => differenceQuotient (U y) v h) (fun y => differenceQuotient (D y) v h)
    ((continuous_differenceQuotient v h).comp hU)
    ((continuous_differenceQuotient v h).comp hD) v ?_ z k
  intro a k
  rw [hSU, hSD]
  exact norm_doubleQuotient_schwartz_le (S a) v h k

def quotientTest (u : ScalarL2 n) (v : E) (h : ℝ) : ScalarL2 n :=
  -(differenceQuotient (differenceQuotient u v h) v (-h))

def quotientTestSchwartz (f : 𝓢(E, ℝ)) (v : E) (h : ℝ) : 𝓢(E, ℝ) :=
  -(differenceQuotientSchwartz (differenceQuotientSchwartz f v h) v (-h))

theorem quotientTestSchwartz_toLp (f : 𝓢(E, ℝ)) (v : E) (h : ℝ) :
    (quotientTestSchwartz f v h).toLp 2 volume = quotientTest (f.toLp 2 volume) v h := by
  change SchwartzMap.toLpCLM ℝ ℝ 2 volume (-_) = _
  rw [map_neg]
  simp only [SchwartzMap.toLpCLM_apply, differenceQuotientSchwartz_toLp, quotientTest]

theorem lineDeriv_quotientTestSchwartz (f : 𝓢(E, ℝ)) (v w : E) (h : ℝ) :
    ∂_{w} (quotientTestSchwartz f v h) = quotientTestSchwartz (∂_{w} f) v h := by
  simp only [quotientTestSchwartz, LineDeriv.lineDerivOp_neg,
    lineDeriv_differenceQuotientSchwartz]

theorem continuous_quotientTest (v : E) (h : ℝ) :
    Continuous (fun u : ScalarL2 n => quotientTest u v h) :=
  ((continuous_differenceQuotient v (-h)).comp (continuous_differenceQuotient v h)).neg

theorem tsupport_differenceQuotientSchwartz_subset (f : 𝓢(E, ℝ)) (v : E) (h : ℝ)
    {K : Set E} (hK : tsupport f ⊆ K) {r : ℝ} (hr : ‖h • v‖ ≤ r) :
    tsupport (differenceQuotientSchwartz f v h) ⊆ cthickening r K := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  by_cases hxshift : x + h • v ∈ tsupport f
  · apply mem_cthickening_of_dist_le x (x + h • v) r K (hK hxshift)
    simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg] using hr
  by_cases hxf : x ∈ tsupport f
  · exact self_subset_cthickening K (hK hxf)
  · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport hxf
    have hshift : f (x + h • v) = 0 := image_eq_zero_of_notMem_tsupport hxshift
    exact False.elim (hx (by simp only [differenceQuotientSchwartz_apply, hzero, hshift,
      sub_self, mul_zero]))

theorem differenceQuotientSchwartz_hasCompactSupport (f : 𝓢(E, ℝ))
    (hf : HasCompactSupport f) (v : E) (h : ℝ) :
    HasCompactSupport (differenceQuotientSchwartz f v h) :=
  (hf.cthickening (r := ‖h • v‖)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_differenceQuotientSchwartz_subset f v h Subset.rfl le_rfl)

theorem quotientTestSchwartz_hasCompactSupport (f : 𝓢(E, ℝ))
    (hf : HasCompactSupport f) (v : E) (h : ℝ) : HasCompactSupport (quotientTestSchwartz f v h) :=
  (differenceQuotientSchwartz_hasCompactSupport _
    (differenceQuotientSchwartz_hasCompactSupport f hf v h) v (-h)).neg

theorem tsupport_quotientTestSchwartz_subset (f : 𝓢(E, ℝ)) (v : E) (h : ℝ)
    {K : Set E} (hK : tsupport f ⊆ K) {r : ℝ} (hr : 0 ≤ r) (hh : ‖h • v‖ ≤ r) :
    tsupport (quotientTestSchwartz f v h) ⊆ cthickening (r + r) K := by
  have hhneg : ‖(-h) • v‖ ≤ r := by simpa only [neg_smul, norm_neg] using hh
  have hfirst := tsupport_differenceQuotientSchwartz_subset f v h hK hh
  have hsecond := tsupport_differenceQuotientSchwartz_subset
    (differenceQuotientSchwartz f v h) v (-h) hfirst hhneg
  change tsupport (-(differenceQuotientSchwartz (differenceQuotientSchwartz f v h) v (-h)
    : E → ℝ)) ⊆ _
  rw [tsupport_neg]
  exact hsecond.trans (cthickening_cthickening_subset hr hr K)

theorem quotientTest_equation_of_denseRange {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (S : α → 𝓢(E, ℝ))
    (U : β → ScalarL2 n) (D : Fin n → β → ScalarL2 n)
    (hU : Continuous U) (hD : ∀ j, Continuous (D j))
    (hSU : ∀ a, U (e a) = (S a).toLp 2 volume)
    (hSD : ∀ j a, D j (e a) = (∂_{EuclideanSpace.single j (1 : ℝ)} (S a)).toLp 2 volume)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) (V : Fin n → ScalarL2 n) (G : ScalarL2 n)
    (v : E) (h : ℝ)
    (hweak : ∀ a,
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (V i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} (quotientTestSchwartz (S a) v h)).toLp 2 volume)) =
        inner ℝ G ((quotientTestSchwartz (S a) v h).toLp 2 volume))
    (z : β) :
    (∑ i, ∑ j, inner ℝ (differenceQuotient (schwartzMultiplier (A i j) (V i)) v h)
      (differenceQuotient (D j z) v h)) = inner ℝ G (quotientTest (U z) v h) := by
  have heq :
      (fun y : β => ∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (V i))
        (quotientTest (D j y) v h)) =
      (fun y : β => inner ℝ G (quotientTest (U y) v h)) := by
    apply he.equalizer
    · apply continuous_finset_sum
      intro i _
      apply continuous_finset_sum
      intro j _
      exact continuous_const.inner ((continuous_quotientTest v h).comp (hD j))
    · exact continuous_const.inner ((continuous_quotientTest v h).comp hU)
    · funext a
      simpa only [Function.comp_apply, hSU, hSD, lineDeriv_quotientTestSchwartz,
        quotientTestSchwartz_toLp] using hweak a
  have h := congrFun heq z
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_differenceQuotient_adjoint]
  simp only [quotientTest, inner_neg_right]

theorem inner_schwartzMultiplier_toLp (A f q : 𝓢(E, ℝ)) :
    inner ℝ (schwartzMultiplier A (f.toLp 2 volume)) (q.toLp 2 volume) =
      ∫ x, A x * f x * q x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [schwartzMultiplier_coe A (f.toLp 2 volume),
    f.coeFn_toLp 2 volume, q.coeFn_toLp 2 volume] with x hm hf hq
  rw [hm, hf, hq]
  simp only [Real.inner_apply]

theorem integrable_schwartz_triple (A f q : 𝓢(E, ℝ)) :
    Integrable (fun x => A x * f x * q x) volume := by
  apply ((Lp.memLp (schwartzMultiplier A (f.toLp 2 volume))).integrable_mul
    (q.memLp 2 volume)).congr
  filter_upwards [schwartzMultiplier_coe A (f.toLp 2 volume),
    f.coeFn_toLp 2 volume] with x hm hf
  simpa only [Pi.mul_apply, hm, hf]

theorem schwartz_coercive_energy (A : Fin n → Fin n → 𝓢(E, ℝ))
    (w : Fin n → 𝓢(E, ℝ)) (ell : ℝ)
    (hpoint : ∀ x, ell * (∑ i, (w i x) ^ 2) ≤
      ∑ i, ∑ j, A i j x * w i x * w j x) :
    ell * (∑ i, ‖(w i).toLp 2 volume‖ ^ 2) ≤
      ∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) ((w i).toLp 2 volume))
        ((w j).toLp 2 volume) := by
  have hsq (i : Fin n) : Integrable (fun x => (w i x) ^ 2) volume :=
    ((w i).memLp 2 volume).integrable_sq
  have htr (i j : Fin n) := integrable_schwartz_triple (A i j) (w i) (w j)
  have hmono := integral_mono
    ((integrable_finsetSum Finset.univ (fun i _ => hsq i)).const_mul ell)
    (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => htr i j))) hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hsq i),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => htr i j))] at hmono
  simp_rw [integral_finsetSum Finset.univ (fun j _ => htr _ j),
    ← inner_schwartzMultiplier_toLp, ← scalar_toLp_norm_sq ((w _).memLp 2 volume)] at hmono
  exact hmono

theorem quadratic_lower_bound_sum {c : ℝ} (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ ξ : Fin n → ℝ, c * ‖ξ‖ ^ 2 ≤ DeTurckNative.quadratic A ξ)
    (ξ : Fin n → ℝ) :
    (c / ((n : ℝ) + 1)) * (∑ i, ξ i ^ 2) ≤ DeTurckNative.quadratic A ξ := by
  have hsum : (∑ i, ξ i ^ 2) ≤ (n : ℝ) * ‖ξ‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, ‖ξ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs, sq_abs] using
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm ξ i)
      _ = _ := by simp
  have hn : 0 < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ (c / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum.trans (by nlinarith [sq_nonneg ‖ξ‖]))
        (div_nonneg hc.le hn.le)
    _ = c * ‖ξ‖ ^ 2 := by field_simp
    _ ≤ _ := hA ξ

theorem quotientSchwartz_coercive_energy (A : Fin n → Fin n → 𝓢(E, ℝ))
    (f : 𝓢(E, ℝ)) {K : Set E} (hfK : tsupport f ⊆ K)
    {r ell : ℝ} (hr : 0 ≤ r) (v : E) (h : ℝ) (hh : ‖h • v‖ ≤ r)
    (hell : ∀ x ∈ cthickening (r + r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j) :
    ell * (∑ i : Fin n,
      ‖differenceQuotient ((∂_{EuclideanSpace.single i (1 : ℝ)} f).toLp 2 volume) v h‖ ^ 2) ≤
      ∑ i, ∑ j,
        inner ℝ
          (schwartzMultiplier (translateSchwartz (h • v) (A i j))
            (differenceQuotient ((∂_{EuclideanSpace.single i (1 : ℝ)} f).toLp 2 volume) v h))
          (differenceQuotient ((∂_{EuclideanSpace.single j (1 : ℝ)} f).toLp 2 volume) v h) := by
  let w : Fin n → 𝓢(E, ℝ) := fun i =>
    differenceQuotientSchwartz (∂_{EuclideanSpace.single i (1 : ℝ)} f) v h
  have hw (i : Fin n) : tsupport (w i) ⊆ cthickening r K :=
    tsupport_differenceQuotientSchwartz_subset _ v h
      ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hfK) hh
  have hpoint (x : E) : ell * (∑ i, (w i x) ^ 2) ≤
      ∑ i, ∑ j, translateSchwartz (h • v) (A i j) x * w i x * w j x := by
    by_cases hx : x ∈ cthickening r K
    · have hshift : x + h • v ∈ cthickening (r + r) K := by
        apply cthickening_cthickening_subset hr hr K
        apply mem_cthickening_of_dist_le (x + h • v) x r (cthickening r K) hx
        simpa only [dist_eq_norm, add_sub_cancel_left] using hh
      simpa only [translateSchwartz_apply] using hell (x + h • v) hshift (fun i => w i x)
    · have hzero (i : Fin n) : w i x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hmem => hx (hw i hmem))
      simp only [hzero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Finset.sum_const_zero, le_refl]
  simpa only [w, differenceQuotientSchwartz_toLp] using
    schwartz_coercive_energy (fun i j => translateSchwartz (h • v) (A i j)) w ell hpoint

theorem quotient_coercive_energy_of_denseRange {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (S : α → 𝓢(E, ℝ))
    (D : Fin n → β → ScalarL2 n) (hD : ∀ i, Continuous (D i))
    (hSD : ∀ i a, D i (e a) = (∂_{EuclideanSpace.single i (1 : ℝ)} (S a)).toLp 2 volume)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {K : Set E} (hSK : ∀ a, tsupport (S a) ⊆ K)
    {r ell : ℝ} (hr : 0 ≤ r) (v : E) (h : ℝ) (hh : ‖h • v‖ ≤ r)
    (hell : ∀ x ∈ cthickening (r + r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (z : β) :
    ell * (∑ i, ‖differenceQuotient (D i z) v h‖ ^ 2) ≤
      ∑ i, ∑ j,
        inner ℝ
          (schwartzMultiplier (translateSchwartz (h • v) (A i j))
            (differenceQuotient (D i z) v h))
          (differenceQuotient (D j z) v h) := by
  have hQ (i : Fin n) : Continuous (fun y : β => differenceQuotient (D i y) v h) :=
    (continuous_differenceQuotient v h).comp (hD i)
  apply he.induction_on (p := fun y =>
    ell * (∑ i, ‖differenceQuotient (D i y) v h‖ ^ 2) ≤
      ∑ i, ∑ j, inner ℝ
        (schwartzMultiplier (translateSchwartz (h • v) (A i j))
          (differenceQuotient (D i y) v h))
        (differenceQuotient (D j y) v h)) z
  · apply isClosed_le
    · apply continuous_const.mul
      apply continuous_finset_sum
      intro i _
      exact (hQ i).norm.pow 2
    · apply continuous_finset_sum
      intro i _
      apply continuous_finset_sum
      intro j _
      exact ((schwartzMultiplier (translateSchwartz (h • v) (A i j))).continuous.comp
        (hQ i)).inner (hQ j)
  · intro a
    simpa only [hSD] using quotientSchwartz_coercive_energy A (S a) (hSK a) hr v h hh hell

theorem exists_schwartz_matrix_derivative_bound (A : Fin n → Fin n → 𝓢(E, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B := by
  let C : Fin n → Fin n → ℝ := fun i j =>
    SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ E ℝ (A i j))
  have hC (i j : Fin n) : 0 ≤ C i j := apply_nonneg _ _
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro i j x
  have hfirst : ‖fderiv ℝ (A i j) x‖ ≤ C i j :=
    (SchwartzMap.fderivCLM ℝ E ℝ (A i j)).norm_le_seminorm ℝ x
  exact hfirst.trans ((Finset.single_le_sum (fun k _ => hC i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hC k l))
      (Finset.mem_univ i)))

theorem norm_coordinateQuotient_le_of_weak_equation {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (S : α → 𝓢(E, ℝ))
    (U : β → ScalarL2 n) (D : Fin n → β → ScalarL2 n)
    (hU : Continuous U) (hD : ∀ j, Continuous (D j))
    (hSU : ∀ a, U (e a) = (S a).toLp 2 volume)
    (hSD : ∀ j a, D j (e a) = (∂_{EuclideanSpace.single j (1 : ℝ)} (S a)).toLp 2 volume)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {K : Set E} (hSK : ∀ a, tsupport (S a) ⊆ K)
    {r ell B : ℝ} (hr : 0 ≤ r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (r + r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (G : ScalarL2 n) (z : β) (k : Fin n) (h : ℝ)
    (hh : ‖h • EuclideanSpace.single k (1 : ℝ)‖ ≤ r)
    (hweak : ∀ a,
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i z))
        ((∂_{EuclideanSpace.single j (1 : ℝ)}
          (quotientTestSchwartz (S a) (EuclideanSpace.single k (1 : ℝ)) h)).toLp 2 volume)) =
        inner ℝ G ((quotientTestSchwartz (S a) (EuclideanSpace.single k (1 : ℝ)) h).toLp 2 volume))
    (i : Fin n) :
    ‖differenceQuotient (D i z) (EuclideanSpace.single k (1 : ℝ)) h‖ ≤
      (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j z‖)) / ell := by
  let v : E := EuclideanSpace.single k (1 : ℝ)
  let w : Fin n → ScalarL2 n := fun j => differenceQuotient (D j z) v h
  let R : Fin n → Fin n → ScalarL2 n := fun i j =>
    schwartzMultiplier (differenceQuotientSchwartz (A i j) v h) (D i z)
  let principal : ℝ := ∑ i, ∑ j,
    inner ℝ (schwartzMultiplier (translateSchwartz (h • v) (A i j)) (w i)) (w j)
  have hv : ‖v‖ = 1 := by simp [v]
  have hprincipal : ell * gradientSize w ^ 2 ≤ principal := by
    rw [gradientSize_sq]
    exact quotient_coercive_energy_of_denseRange e he S D hD hSD A hSK hr v h hh hell z
  have hR (i j : Fin n) : ‖R i j‖ ≤ B * ‖D i z‖ := by
    apply norm_schwartzMultiplier_le
    intro x
    simpa only [hv, mul_one] using
      norm_differenceQuotientSchwartz_apply_le (A i j) v hB (hAB i j) h x
  have htest : ‖quotientTest (U z) v h‖ ≤ gradientSize w := by
    rw [quotientTest, norm_neg]
    exact (norm_doubleQuotient_le_of_denseRange e he S U (D k) hU (hD k) v hSU
      (hSD k) z h (-h)).trans (norm_le_gradientSize w k)
  have heq : principal + (∑ i, ∑ j, inner ℝ (R i j) (w j)) =
      inner ℝ G (quotientTest (U z) v h) := by
    have htesteq := quotientTest_equation_of_denseRange e he S U D hU hD hSU hSD A
      (fun i => D i z) G v h hweak z
    simpa only [differenceQuotient_schwartzMultiplier, inner_add_left,
      Finset.sum_add_distrib, principal, R, w] using htesteq
  simpa only [Fintype.card_fin, w] using
    norm_le_of_discrete_energy (fun j => D j z) w R G (quotientTest (U z) v h)
      hEll hB hprincipal hR htest heq i

theorem exists_secondDerivatives_of_weak_equation {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (S : α → 𝓢(E, ℝ))
    (U : β → ScalarL2 n) (D : Fin n → β → ScalarL2 n)
    (hU : Continuous U) (hD : ∀ j, Continuous (D j))
    (hSU : ∀ a, U (e a) = (S a).toLp 2 volume)
    (hSD : ∀ j a, D j (e a) = (∂_{EuclideanSpace.single j (1 : ℝ)} (S a)).toLp 2 volume)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {K : Set E} (hSK : ∀ a, tsupport (S a) ⊆ K)
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (r + r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (G : ScalarL2 n) (z : β)
    (hweak : ∀ k h, ‖h • EuclideanSpace.single k (1 : ℝ)‖ ≤ r → ∀ a,
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i z))
        ((∂_{EuclideanSpace.single j (1 : ℝ)}
          (quotientTestSchwartz (S a) (EuclideanSpace.single k (1 : ℝ)) h)).toLp 2 volume)) =
        inner ℝ G ((quotientTestSchwartz (S a) (EuclideanSpace.single k (1 : ℝ)) h).toLp 2 volume)) :
    ∃ W : Fin n → Fin n → ScalarL2 n, ∀ i k,
      ‖W i k‖ ≤ (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j z‖)) / ell ∧
        ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ →
          inner ℝ (W i k) (φ.toLp 2 volume) =
            -(∫ x, D i z x * fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))) := by
  have hbound (i k : Fin n) : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ‖differenceQuotient (D i z) (EuclideanSpace.single k (1 : ℝ)) h‖ ≤
        (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j z‖)) / ell := by
    have hnear : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ∈ ball (0 : ℝ) r :=
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℝ) hr)
    filter_upwards [hnear] with h hh
    have habs : ‖h‖ < r := by simpa only [mem_ball, dist_zero_right] using hh
    have hsmall : ‖h • EuclideanSpace.single k (1 : ℝ)‖ ≤ r := by
      simpa only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one] using habs.le
    exact norm_coordinateQuotient_le_of_weak_equation e he S U D hU hD hSU hSD A hSK
      hr.le hEll hB hell hAB G z k h hsmall (hweak k h hsmall) i
  choose W hW using fun i k =>
    exists_weakCoordinateDerivative_of_bounded_differenceQuotients (D i z) k (hbound i k)
  exact ⟨W, hW⟩

theorem exists_secondDerivatives_of_weak_equation_integrable
    {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (S : α → 𝓢(E, ℝ))
    (U : β → ScalarL2 n) (D : Fin n → β → ScalarL2 n)
    (hU : Continuous U) (hD : ∀ j, Continuous (D j))
    (hSU : ∀ a, U (e a) = (S a).toLp 2 volume)
    (hSD : ∀ j a,
      D j (e a) = (∂_{EuclideanSpace.single j (1 : ℝ)} (S a)).toLp 2 volume)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {K : Set E} (hSK : ∀ a, tsupport (S a) ⊆ K)
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (r + r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (G : ScalarL2 n) (z : β) (hL1 : ∀ i, Integrable (D i z : E → ℝ) volume)
    (hweak : ∀ k h, ‖h • EuclideanSpace.single k (1 : ℝ)‖ ≤ r → ∀ a,
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i z))
        ((∂_{EuclideanSpace.single j (1 : ℝ)}
          (quotientTestSchwartz (S a) (EuclideanSpace.single k (1 : ℝ)) h)).toLp 2 volume)) =
        inner ℝ G
          ((quotientTestSchwartz (S a) (EuclideanSpace.single k (1 : ℝ)) h).toLp 2 volume)) :
    ∃ W : Fin n → Fin n → ScalarL2 n, ∀ i k,
      ‖W i k‖ ≤ (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j z‖)) / ell ∧
        ∀ φ : 𝓢(E, ℝ),
          inner ℝ (W i k) (φ.toLp 2 volume) =
            -(∫ x, D i z x * fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))) := by
  have hbound (i k : Fin n) : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ‖differenceQuotient (D i z) (EuclideanSpace.single k (1 : ℝ)) h‖ ≤
        (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j z‖)) / ell := by
    have hnear : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ∈ ball (0 : ℝ) r :=
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℝ) hr)
    filter_upwards [hnear] with h hh
    have habs : ‖h‖ < r := by simpa only [mem_ball, dist_zero_right] using hh
    have hsmall : ‖h • EuclideanSpace.single k (1 : ℝ)‖ ≤ r := by
      simpa only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one] using habs.le
    exact norm_coordinateQuotient_le_of_weak_equation e he S U D hU hD hSU hSD A hSK
      hr.le hEll hB hell hAB G z k h hsmall (hweak k h hsmall) i
  choose W hW using fun i k =>
    exists_weakCoordinateDerivative_of_bounded_differenceQuotients_integrable
      (D i z) (hL1 i) k (hbound i k)
  exact ⟨W, hW⟩

end PoincareConjecture.DeTurckGeneratorRegularityNative

end
