




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy











open Set Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}

private def D (v : Spacetime n) (f : Spacetime n → ℝ) : Spacetime n → ℝ :=
  fun y => fderiv ℝ f y v

private structure Test (U : Set (Spacetime n)) (f : Spacetime n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  compact : HasCompactSupport f
  subset : tsupport f ⊆ U

private theorem D_smooth {f : Spacetime n → ℝ} (hf : ContDiff ℝ ∞ f) (v : Spacetime n) :
    ContDiff ℝ ∞ (D v f) := (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem D_smoothOn (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (v : Spacetime n) :
    ContDiffOn ℝ ∞ (D v f) U := (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem Test.deriv {f : Spacetime n → ℝ} (hf : Test U f) (v : Spacetime n) :
    Test U (D v f) :=
  ⟨D_smooth hf.smooth v, hf.compact.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans hf.subset⟩

private theorem smooth_of_support (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport f
  · exact (hf y (hs hy)).contDiffAt (hU.mem_nhds (hs hy))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

private theorem Test.mul (hU : IsOpen U) {q f : Spacetime n → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hf : Test U f) : Test U (fun y => q y * f y) := by
  have hs : tsupport (fun y => q y * f y) ⊆ U := tsupport_mul_subset_right.trans hf.subset
  exact ⟨smooth_of_support hU (hq.mul hf.smooth.contDiffOn) hs, hf.compact.mul_left, hs⟩

private theorem Test.add {f g : Spacetime n → ℝ} (hf : Test U f) (hg : Test U g) :
    Test U (fun y => f y + g y) := by
  refine ⟨hf.smooth.add hg.smooth, hf.compact.add hg.compact, ?_⟩
  apply (closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport g))).trans
    (union_subset hf.subset hg.subset)
  intro y hy
  by_contra hn
  simp only [mem_union, not_or] at hn
  exact hy (by change f y + g y = 0; rw [image_eq_zero_of_notMem_tsupport hn.1,
    image_eq_zero_of_notMem_tsupport hn.2]; ring)

private theorem Test.neg {f : Spacetime n → ℝ} (hf : Test U f) :
    Test U (fun y => -f y) := by
  refine ⟨hf.smooth.neg, hf.compact.neg, ?_⟩
  change tsupport (-f) ⊆ U
  simpa only [tsupport_neg] using hf.subset

private theorem Test.sub {f g : Spacetime n → ℝ} (hf : Test U f) (hg : Test U g) :
    Test U (fun y => f y - g y) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem Test.sum {ι : Type*} (s : Finset ι) {f : ι → Spacetime n → ℝ}
    (hf : ∀ i ∈ s, Test U (f i)) : Test U (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show Test U (fun _ : Spacetime n => (0 : ℝ)) from
      ⟨contDiff_const, HasCompactSupport.zero, by simp⟩)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem Test.integrable_mul {f ψ : Spacetime n → ℝ}
    (hψ : Test U ψ) (hf : LocallyIntegrableOn f U volume) :
    Integrable (fun y => f y * ψ y) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f ψ).trans (subset_tsupport ψ))).mp
  exact (hf.integrableOn_compact_subset hψ.subset hψ.compact).mul_continuousOn
    hψ.smooth.continuous.continuousOn hψ.compact

private theorem Test.restrict_pair {f ψ : Spacetime n → ℝ} (hψ : Test U ψ) :
    (∫ y in U, f y * ψ y) = ∫ y, f y * ψ y := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ.subset h)), mul_zero]

private theorem D_neg {f : Spacetime n → ℝ} (v : Spacetime n) :
    D v (fun y => -f y) = fun y => -D v f y := by
  funext y
  change fderiv ℝ (-f) y v = -fderiv ℝ f y v
  rw [fderiv_neg]
  rfl

private theorem D_add {f g : Spacetime n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v : Spacetime n) :
    D v (fun y => f y + g y) = fun y => D v f y + D v g y := by
  funext y
  simp only [D, fderiv_fun_add (hf.differentiable (by simp) y)
    (hg.differentiable (by simp) y), add_apply]

private theorem D_sub {f g : Spacetime n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v : Spacetime n) :
    D v (fun y => f y - g y) = fun y => D v f y - D v g y := by
  funext y
  simp only [D, fderiv_fun_sub (hf.differentiable (by simp) y)
    (hg.differentiable (by simp) y), sub_apply]

private theorem D_sum {ι : Type*} (s : Finset ι) {f : ι → Spacetime n → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (v : Spacetime n) :
    D v (fun y => ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, D v (f i) y := by
  funext y
  simp only [D, fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) y),
    sum_apply]

private theorem D_comm {f : Spacetime n → ℝ} (hf : ContDiff ℝ ∞ f)
    (v w : Spacetime n) : D v (D w f) = D w (D v f) := by
  funext y
  exact directionalSecond_comm f hf v w y

private theorem D_mul_test (hU : IsOpen U) {q f : Spacetime n → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hf : Test U f) (v : Spacetime n) :
    D v (fun y => q y * f y) = fun y => D v q y * f y + q y * D v f y := by
  funext y
  by_cases hy : y ∈ U
  · dsimp only [D]
    rw [fderiv_fun_mul (((hq y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (hf.smooth.differentiable (by simp) y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  · have hz : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hf.subset h))
    have hd : D v f y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy ((hf.deriv v).subset h))
    have hp : D v (fun y => q y * f y) y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (((hf.mul hU hq).deriv v).subset h))
    simp only [hz, hd, hp, mul_zero, add_zero]

private theorem Test.adjoint (hU : IsOpen U) {C : Coefficients n}
    (hC : C.IsSmoothOn U) {φ : Spacetime n → ℝ} (hφ : Test U φ) :
    Test U (C.adjoint φ) := by
  exact (((hφ.deriv (0, 1)).neg.sub
    (Test.sum Finset.univ (fun i _ => Test.sum Finset.univ (fun j _ =>
      (((hφ.mul hU (hC.1 i j)).deriv (spatialDirection i)).deriv (spatialDirection j)))))).sub
    (Test.sum Finset.univ (fun i _ => (hφ.mul hU (hC.2.1 i)).deriv (spatialDirection i)))).add
    (hφ.mul hU hC.2.2)

private theorem D_adjoint (hU : IsOpen U) {C : Coefficients n}
    (hC : C.IsSmoothOn U) {φ : Spacetime n → ℝ} (hφ : Test U φ) (v : Spacetime n) :
    D v (C.adjoint φ) = fun y => C.adjoint (D v φ) y -
      (∑ i, ∑ j, spatialDeriv j (spatialDeriv i
        (fun x => D v (C.principal i j) x * φ x)) y) -
      (∑ i, spatialDeriv i (fun x => D v (C.drift i) x * φ x) y) +
      D v C.zeroth y * φ y := by
  let A := fun i j y => C.principal i j y * φ y
  let B := fun i y => C.drift i y * φ y
  let Z := fun y => C.zeroth y * φ y
  let A0 := fun i j y => C.principal i j y * D v φ y
  let A1 := fun i j y => D v (C.principal i j) y * φ y
  let B0 := fun i y => C.drift i y * D v φ y
  let B1 := fun i y => D v (C.drift i) y * φ y
  have hA (i j) : Test U (A i j) := hφ.mul hU (hC.1 i j)
  have hB (i) : Test U (B i) := hφ.mul hU (hC.2.1 i)
  have hZ : Test U Z := hφ.mul hU hC.2.2
  have hA0 (i j) : Test U (A0 i j) := (hφ.deriv v).mul hU (hC.1 i j)
  have hA1 (i j) : Test U (A1 i j) := hφ.mul hU (D_smoothOn hU (hC.1 i j) v)
  have hB0 (i) : Test U (B0 i) := (hφ.deriv v).mul hU (hC.2.1 i)
  have hB1 (i) : Test U (B1 i) := hφ.mul hU (D_smoothOn hU (hC.2.1 i) v)
  have hDA (i j) : D v (D (spatialDirection j) (D (spatialDirection i) (A i j))) =
      fun y => D (spatialDirection j) (D (spatialDirection i) (A0 i j)) y +
        D (spatialDirection j) (D (spatialDirection i) (A1 i j)) y := by
    rw [D_comm ((hA i j).deriv (spatialDirection i)).smooth v (spatialDirection j),
      D_comm (hA i j).smooth v (spatialDirection i)]
    have he : D v (A i j) = fun y => A1 i j y + A0 i j y :=
      D_mul_test hU (hC.1 i j) hφ v
    rw [he, D_add (hA1 i j).smooth (hA0 i j).smooth (spatialDirection i),
      D_add ((hA1 i j).deriv (spatialDirection i)).smooth
        ((hA0 i j).deriv (spatialDirection i)).smooth (spatialDirection j)]
    funext y
    ring
  have hDB (i) : D v (D (spatialDirection i) (B i)) =
      fun y => D (spatialDirection i) (B0 i) y + D (spatialDirection i) (B1 i) y := by
    rw [D_comm (hB i).smooth v (spatialDirection i)]
    have he : D v (B i) = fun y => B1 i y + B0 i y :=
      D_mul_test hU (hC.2.1 i) hφ v
    rw [he, D_add (hB1 i).smooth (hB0 i).smooth (spatialDirection i)]
    funext y
    ring
  have hDZ : D v Z = fun y => C.zeroth y * D v φ y + D v C.zeroth y * φ y := by
    rw [show D v Z = fun y => D v C.zeroth y * φ y + C.zeroth y * D v φ y from
      D_mul_test hU hC.2.2 hφ v]
    funext y
    ring
  let SA := fun y => ∑ i, ∑ j, D (spatialDirection j) (D (spatialDirection i) (A i j)) y
  let SB := fun y => ∑ i, D (spatialDirection i) (B i) y
  have hSA : Test U SA := Test.sum Finset.univ (fun i _ => Test.sum Finset.univ
    (fun j _ => ((hA i j).deriv (spatialDirection i)).deriv (spatialDirection j)))
  have hSB : Test U SB := Test.sum Finset.univ (fun i _ => (hB i).deriv (spatialDirection i))
  have he : C.adjoint φ = fun y => -D (0, 1) φ y - SA y - SB y + Z y := rfl
  rw [he, D_add ((((hφ.deriv (0, 1)).neg.sub hSA).sub hSB).smooth) hZ.smooth v,
    D_sub (((hφ.deriv (0, 1)).neg.sub hSA).smooth) hSB.smooth v,
    D_sub (hφ.deriv (0, 1)).neg.smooth hSA.smooth v,
    D_neg, D_comm hφ.smooth v (0, 1), hDZ]
  have hDSA : D v SA = fun y =>
      (∑ i, ∑ j, D (spatialDirection j) (D (spatialDirection i) (A0 i j)) y) +
      (∑ i, ∑ j, D (spatialDirection j) (D (spatialDirection i) (A1 i j)) y) := by
    rw [show D v SA = fun y => ∑ i, D v
      (fun x => ∑ j, D (spatialDirection j) (D (spatialDirection i) (A i j)) x) y from
      D_sum Finset.univ (fun i _ => (Test.sum Finset.univ
        (fun j _ => ((hA i j).deriv (spatialDirection i)).deriv (spatialDirection j))).smooth) v]
    simp_rw [D_sum Finset.univ (fun j _ =>
      (((hA _ j).deriv (spatialDirection _)).deriv (spatialDirection j)).smooth) v, hDA]
    funext y
    simp only [Finset.sum_add_distrib]
  have hDSB : D v SB = fun y => (∑ i, D (spatialDirection i) (B0 i) y) +
      (∑ i, D (spatialDirection i) (B1 i) y) := by
    rw [show D v SB = fun y => ∑ i, D v (D (spatialDirection i) (B i)) y from
      D_sum Finset.univ (fun i _ => ((hB i).deriv (spatialDirection i)).smooth) v]
    simp_rw [hDB]
    funext y
    simp only [Finset.sum_add_distrib]
  rw [hDSA, hDSB]
  funext y
  unfold Coefficients.adjoint A0 A1 B0 B1 D timeDeriv spatialDeriv
  ring

private def pair (f ψ : Spacetime n → ℝ) : ℝ := ∫ y, f y * ψ y

private theorem pair_add {f ψ θ : Spacetime n → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hψ : Test U ψ) (hθ : Test U θ) :
    pair f (fun y => ψ y + θ y) = pair f ψ + pair f θ := by
  simp only [pair, mul_add]
  exact integral_add (hψ.integrable_mul hf) (hθ.integrable_mul hf)

private theorem pair_sub {f ψ θ : Spacetime n → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hψ : Test U ψ) (hθ : Test U θ) :
    pair f (fun y => ψ y - θ y) = pair f ψ - pair f θ := by
  simp only [pair, mul_sub]
  exact integral_sub (hψ.integrable_mul hf) (hθ.integrable_mul hf)

private theorem pair_sum {ι : Type*} (s : Finset ι)
    {f : Spacetime n → ℝ} {ψ : ι → Spacetime n → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hψ : ∀ i ∈ s, Test U (ψ i)) :
    pair f (fun y => ∑ i ∈ s, ψ i y) = ∑ i ∈ s, pair f (ψ i) := by
  simp only [pair, Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => (hψ i hi).integrable_mul hf)

private theorem weak_pair {f g : Spacetime n → ℝ} (v : Spacetime n)
    (hweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ y in U, ψ y * g y) = -(∫ y in U, D v ψ y * f y))
    {ψ : Spacetime n → ℝ} (hψ : Test U ψ) : pair g ψ = -pair f (D v ψ) := by
  have hh := hweak ψ hψ.smooth hψ.compact hψ.subset
  simp only [mul_comm] at hh
  rw [hψ.restrict_pair, (hψ.deriv v).restrict_pair] at hh
  exact hh



theorem differentiated_inhomogeneous_pairing
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u w f f_v : Spacetime n → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hf : LocallyIntegrableOn f U volume)
    (hf_v : LocallyIntegrableOn f_v U volume)
    (heq : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ y, u y * C.adjoint ψ y) = ∫ y, ψ y * f y)
    {g : Fin n → Spacetime n → ℝ}
    {H : Fin n → Fin n → Spacetime n → ℝ} (v : Spacetime n)
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hH : ∀ i j, LocallyIntegrableOn (H i j) U volume)
    (hw : LocallyIntegrableOn w U volume)
    (hgweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    (hHweak : ∀ i j (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * H i j y) = -(∫ y in U, spatialDeriv i ψ y * g j y))
    (hwweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * w y) = -(∫ y in U, fderiv ℝ ψ y v * u y))
    (hfweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * f_v y) = -(∫ y in U, fderiv ℝ ψ y v * f y))
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y, w y * C.adjoint φ y) =
      ∫ y, φ y * (f_v y +
        (∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
        (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y) := by
  have Tφ : Test U φ := ⟨hφ, hφc, hφU⟩
  let A := fun i j y => D v (C.principal i j) y * φ y
  let B := fun i y => D v (C.drift i) y * φ y
  let Z := fun y => D v C.zeroth y * φ y
  have TA (i j) : Test U (A i j) := Tφ.mul hU (D_smoothOn hU (hC.1 i j) v)
  have TB (i) : Test U (B i) := Tφ.mul hU (D_smoothOn hU (hC.2.1 i) v)
  have TZ : Test U Z := Tφ.mul hU (D_smoothOn hU hC.2.2 v)
  let SA := fun y => ∑ i, ∑ j, D (spatialDirection j) (D (spatialDirection i) (A i j)) y
  let SB := fun y => ∑ i, D (spatialDirection i) (B i) y
  have TSA : Test U SA := Test.sum Finset.univ (fun i _ => Test.sum Finset.univ
    (fun j _ => ((TA i j).deriv (spatialDirection i)).deriv (spatialDirection j)))
  have TSB : Test U SB := Test.sum Finset.univ (fun i _ => (TB i).deriv (spatialDirection i))
  have Tadj : Test U (C.adjoint (D v φ)) := (Tφ.deriv v).adjoint hU hC
  have hcancel : pair u (C.adjoint (D v φ)) = pair f (D v φ) := by
    simpa only [pair, mul_comm] using
      heq (D v φ) (Tφ.deriv v).smooth (Tφ.deriv v).compact (Tφ.deriv v).subset
  have hfderiv := weak_pair v hfweak Tφ
  have hwtest := weak_pair v hwweak (Tφ.adjoint hU hC)
  have hexpand : pair u (D v (C.adjoint φ)) =
      pair u (C.adjoint (D v φ)) - pair u SA - pair u SB + pair u Z := by
    rw [D_adjoint hU hC Tφ v]
    exact (pair_add hu ((Tadj.sub TSA).sub TSB) TZ).trans
      (by rw [pair_sub hu (Tadj.sub TSA) TSB, pair_sub hu Tadj TSA])
  have hAweak (i j) : pair u (D (spatialDirection j) (D (spatialDirection i) (A i j))) =
      pair (H i j) (A i j) := by
    have h1 := weak_pair (spatialDirection j) (hgweak j) ((TA i j).deriv (spatialDirection i))
    have h2 := weak_pair (spatialDirection i) (hHweak i j) (TA i j)
    linarith only [h1, h2]
  have hBweak (i) : pair u (D (spatialDirection i) (B i)) = -pair (g i) (B i) := by
    have h1 := weak_pair (spatialDirection i) (hgweak i) (TB i)
    linarith only [h1]
  have hSA : pair u SA = ∑ i, ∑ j, pair (H i j) (A i j) := by
    rw [show pair u SA = ∑ i, pair u (fun y =>
      ∑ j, D (spatialDirection j) (D (spatialDirection i) (A i j)) y) from
      pair_sum Finset.univ hu (fun i _ => Test.sum Finset.univ
        (fun j _ => ((TA i j).deriv (spatialDirection i)).deriv (spatialDirection j)))]
    simp_rw [pair_sum Finset.univ hu (fun j _ =>
      ((TA _ j).deriv (spatialDirection _)).deriv (spatialDirection j)), hAweak]
  have hSB : pair u SB = -(∑ i, pair (g i) (B i)) := by
    rw [show pair u SB = ∑ i, pair u (D (spatialDirection i) (B i)) from
      pair_sum Finset.univ hu (fun i _ => (TB i).deriv (spatialDirection i))]
    simp only [hBweak, Finset.sum_neg_distrib]
  rw [hexpand, hcancel, hSA, hSB] at hwtest
  have hHA (i j) : Integrable (fun y => H i j y * A i j y) := (TA i j).integrable_mul (hH i j)
  have hgB (i) : Integrable (fun y => g i y * B i y) := (TB i).integrable_mul (hg i)
  have huZ : Integrable (fun y => u y * Z y) := TZ.integrable_mul hu
  have hHAs : Integrable (fun y => ∑ i, ∑ j, H i j y * A i j y) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hHA i j))
  have hgBs : Integrable (fun y => ∑ i, g i y * B i y) :=
    integrable_finsetSum _ (fun i _ => hgB i)
  have hpoint (y) : φ y * ((∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
      (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y) =
      (∑ i, ∑ j, H i j y * A i j y) - (∑ i, g i y * B i y) - u y * Z y := by
    simp only [A, B, Z, D, mul_sub, Finset.mul_sum]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · apply Finset.sum_congr rfl
        intro i hi
        ring
    · ring
  have hright : (∫ y, φ y * ((∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
        (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y)) =
      (∑ i, ∑ j, pair (H i j) (A i j)) - (∑ i, pair (g i) (B i)) - pair u Z := by
    calc
      _ = ∫ y, (∑ i, ∑ j, H i j y * A i j y) - (∑ i, g i y * B i y) - u y * Z y := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact hpoint y
      _ = _ := by
        have h1 := integral_sub (hHAs.sub hgBs) huZ
        have h2 := integral_sub hHAs hgBs
        simp only [Pi.sub_apply] at h1 h2
        rw [h1, h2,
          integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hHA i j)),
          integral_finsetSum _ (fun i _ => hgB i)]
        simp_rw [integral_finsetSum _ (fun j _ => hHA _ j)]
        rfl
  have hcommI : Integrable (fun y => φ y *
      ((∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
        (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y)) :=
    ((hHAs.sub hgBs).sub huZ).congr (Filter.Eventually.of_forall fun y => (hpoint y).symm)
  have hfull : (∫ y, φ y * (f_v y +
      (∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
        (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y)) =
      pair f_v φ + ∫ y, φ y *
      ((∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
        (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y) := by
    calc
      _ = ∫ y, f_v y * φ y + φ y *
          ((∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
            (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := integral_add (Tφ.integrable_mul hf_v) hcommI
  rw [hfull, hright]
  change pair w (C.adjoint φ) = _
  linarith only [hwtest, hfderiv]


theorem WeakSolutionOn.differentiated_pairing
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u w : Spacetime n → ℝ} (hu : WeakSolutionOn C u U)
    {g : Fin n → Spacetime n → ℝ}
    {H : Fin n → Fin n → Spacetime n → ℝ} (v : Spacetime n)
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hH : ∀ i j, LocallyIntegrableOn (H i j) U volume)
    (hw : LocallyIntegrableOn w U volume)
    (hgweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    (hHweak : ∀ i j (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * H i j y) = -(∫ y in U, spatialDeriv i ψ y * g j y))
    (hwweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * w y) = -(∫ y in U, fderiv ℝ ψ y v * u y))
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y, w y * C.adjoint φ y) =
      ∫ y, φ y * ((∑ i, ∑ j, fderiv ℝ (C.principal i j) y v * H i j y) -
        (∑ i, fderiv ℝ (C.drift i) y v * g i y) - fderiv ℝ C.zeroth y v * u y) := by
  simpa only [zero_add] using differentiated_inhomogeneous_pairing hU hC hu.1
    (f := fun _ => 0) (f_v := fun _ => 0) locallyIntegrableOn_zero locallyIntegrableOn_zero
    (fun ψ hψ hψc hψU => by simpa using hu.2 ψ hψ hψc hψU)
    v hg hH hw hgweak hHweak hwweak (fun ψ _ _ _ => by simp) hφ hφc hφU

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
