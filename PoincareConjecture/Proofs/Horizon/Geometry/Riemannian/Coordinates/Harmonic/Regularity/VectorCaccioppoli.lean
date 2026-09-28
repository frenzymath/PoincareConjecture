import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.WeakGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorPowers

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

private theorem abs_inner_le_sqrt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    |inner ℝ u v| ≤ Real.sqrt (inner ℝ u u) * Real.sqrt (inner ℝ v v) := by
  rw [← norm_eq_sqrt_real_inner, ← norm_eq_sqrt_real_inner]
  exact abs_real_inner_le_norm u v

private theorem abs_sum_inner_le_sqrt {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : ι → E) :
    |∑ i, inner ℝ (A i) (B i)| ≤
      Real.sqrt (∑ i, inner ℝ (A i) (A i)) *
        Real.sqrt (∑ i, inner ℝ (B i) (B i)) := by
  simp_rw [real_inner_self_eq_norm_sq]
  calc
    _ ≤ ∑ i, |inner ℝ (A i) (B i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖A i‖ * ‖B i‖ := Finset.sum_le_sum fun i _ => abs_real_inner_le_norm _ _
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

private theorem abs_sum_mul_inner_le_sqrt {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ι → ℝ) (A : ι → E) (v : E) :
    |∑ i, c i * inner ℝ (A i) v| ≤
      Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, inner ℝ (A i) (A i)) *
        Real.sqrt (inner ℝ v v) := by
  simp_rw [real_inner_self_eq_norm_sq]
  rw [Real.sqrt_sq (norm_nonneg v)]
  calc
    _ ≤ ∑ i, |c i * inner ℝ (A i) v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (‖A i‖ * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = (∑ i, |c i| * ‖A i‖) * ‖v‖ := by
      simp only [Finset.sum_mul, mul_assoc]
    _ ≤ (Real.sqrt (∑ i, |c i| ^ 2) * Real.sqrt (∑ i, ‖A i‖ ^ 2)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _)
        (norm_nonneg _)
    _ = _ := by simp only [sq_abs]

private theorem power_test_absorption {p : ℝ} (hp : 1 ≤ p)
    (h w e y z a : ℝ) :
    2 * h * w * e * y + a * (2 * h * w * e + (2 * p - 2) * h ^ 2 * z + h ^ 2 * y) ≤
      h ^ 2 * y ^ 2 / 2 + (p - 1) * h ^ 2 * z ^ 2 +
        5 * w ^ 2 * e ^ 2 + (p + 1) * h ^ 2 * a ^ 2 := by
  nlinarith only [sq_nonneg (h * y / 2 - 2 * w * e),
    sq_nonneg (h * y / 2 - h * a), sq_nonneg (w * e - h * a),
    mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (h * (z - a)))]

private theorem rpow_weight_sq {w : ℝ} (hw : 0 < w) (p : ℝ) :
    w ^ (2 * p - 2) * w ^ 2 = (w ^ p) ^ 2 := by
  rw [← Real.rpow_mul_natCast hw.le p 2, ← Real.rpow_two,
    ← Real.rpow_add hw]
  congr 1
  ring

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem metric_inner_self_nonneg (x : EuclideanSpace ℝ (Fin n))
    (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

theorem regularized_power_test_lower (D : LeviCivitaData g)
    {V X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : ContDiff ℝ ∞ V) (hη : ContDiff ℝ ∞ η)
    {ε p : ℝ} (hε : 0 < ε) (hp : 1 ≤ p) (x : EuclideanSpace ℝ (Fin n)) :
    let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
    let Z := fun y => (η y ^ 2 * w y ^ (2 * p - 2)) • V y
    (p - 1 / 2) * (η x ^ 2 * w x ^ (2 * p - 2) *
      g.inner x (D.gradient w x) (D.gradient w x)) ≤
      (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection Z x (g.orthonormalBasis x i))) +
      (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
        (D.connection Z x (g.orthonormalBasis x i))) +
      5 * ((w x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)) +
      (p + 1) * (η x ^ 2 * w x ^ (2 * p - 2) *
        ∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
          (D.connection X x (g.orthonormalBasis x i))) := by
  let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
  let Z := fun y => (η y ^ 2 * w y ^ (2 * p - 2)) • V y
  let b := g.orthonormalBasis x
  let A := ∑ i, g.inner x (D.connection V x (b i)) (D.connection V x (b i))
  let B := ∑ i, g.inner x (D.connection X x (b i)) (D.connection X x (b i))
  let W := g.inner x (D.gradient w x) (D.gradient w x)
  let E := g.inner x (D.gradient η x) (D.gradient η x)
  let y := Real.sqrt A
  let a := Real.sqrt B
  let z := Real.sqrt W
  let e := Real.sqrt E
  let s := w x ^ (2 * p - 2)
  let t := w x ^ (2 * p - 3)
  let C := ∑ i, g.inner x (D.connection X x (b i)) (D.connection V x (b i))
  let Tη := ∑ i, mvfderiv (𝓡 n) η x (b i) * g.inner x (D.connection X x (b i)) (V x)
  let Tw := ∑ i, mvfderiv (𝓡 n) w x (b i) * g.inner x (D.connection X x (b i)) (V x)
  let SX := ∑ i, g.inner x (D.connection X x (b i)) (D.connection Z x (b i))
  let SV := ∑ i, g.inner x (D.connection V x (b i)) (D.connection Z x (b i))
  have hVs := contMDiff_vectorSpace_iff_contDiff.mpr hV
  have hηs := contMDiff_iff_contDiff.mpr hη
  have hwpos : 0 < w x := regularized_vector_norm_pos (g := g) V hε x
  have hw2 : w x ^ 2 = g.inner x (V x) (V x) + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp hwpos).le
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => metric_inner_self_nonneg x _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => metric_inner_self_nonneg x _
  have hW : 0 ≤ W := metric_inner_self_nonneg x _
  have hE : 0 ≤ E := metric_inner_self_nonneg x _
  have hy2 : y ^ 2 = A := Real.sq_sqrt hA
  have ha2 : a ^ 2 = B := Real.sq_sqrt hB
  have hz2 : z ^ 2 = W := Real.sq_sqrt hW
  have he2 : e ^ 2 = E := Real.sq_sqrt hE
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.rpow_nonneg hwpos.le _
  have ht : 0 ≤ t := Real.rpow_nonneg hwpos.le _
  have hq : 0 ≤ 2 * p - 2 := by linarith
  have hWA : W ≤ A := D.gradient_regularized_vector_norm_le hVs hε x
  have hzy : z ≤ y := Real.sqrt_le_sqrt hWA
  have htw : t * w x = s := by
    dsimp [t, s]
    rw [← Real.rpow_add_one hwpos.ne']
    congr 1
    ring
  have hsw : w x ^ (2 * p - 1) = s * w x := by
    dsimp [s]
    rw [← Real.rpow_add_one hwpos.ne']
    congr 1
    ring
  have hsp : s * w x ^ 2 = (w x ^ p) ^ 2 := rpow_weight_sq hwpos p
  have hVnorm : Real.sqrt (g.inner x (V x) (V x)) ≤ w x := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hwpos.le, by linarith⟩
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hC : |C| ≤ a * y :=
    abs_sum_inner_le_sqrt (fun i => D.connection X x (b i))
      (fun i => D.connection V x (b i))
  have hTη : |Tη| ≤ e * a * w x := by
    have h := abs_sum_mul_inner_le_sqrt (fun i => mvfderiv (𝓡 n) η x (b i))
      (fun i => D.connection X x (b i)) (V x)
    change |Tη| ≤ Real.sqrt (∑ i, (mvfderiv (𝓡 n) η x (b i)) ^ 2) * a *
      Real.sqrt (g.inner x (V x) (V x)) at h
    rw [← D.gradient_normSq_eq_sum_mvfderiv_sq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hVnorm (mul_nonneg he ha))
  have hTw : |Tw| ≤ z * a * w x := by
    have h := abs_sum_mul_inner_le_sqrt (fun i => mvfderiv (𝓡 n) w x (b i))
      (fun i => D.connection X x (b i)) (V x)
    change |Tw| ≤ Real.sqrt (∑ i, (mvfderiv (𝓡 n) w x (b i)) ^ 2) * a *
      Real.sqrt (g.inner x (V x) (V x)) at h
    rw [← D.gradient_normSq_eq_sum_mvfderiv_sq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hVnorm (mul_nonneg hz ha))
  have hcross : |g.inner x (D.gradient η x) (D.gradient w x)| ≤ e * y :=
    (abs_inner_le_sqrt (D.gradient η x) (D.gradient w x)).trans
      (mul_le_mul_of_nonneg_left hzy he)
  have hSX : SX = η x ^ 2 * s * C + 2 * η x * s * Tη +
      (2 * p - 2) * η x ^ 2 * t * Tw :=
    D.sum_inner_connection_regularized_power_cross X hVs hηs hε p x
  have hSXabs : |SX| ≤ s *
      (|η x| ^ 2 * a * y + 2 * |η x| * w x * e * a +
        (2 * p - 2) * |η x| ^ 2 * z * a) := by
    rw [hSX]
    calc
      _ ≤ |η x ^ 2 * s * C| + |2 * η x * s * Tη| +
          |(2 * p - 2) * η x ^ 2 * t * Tw| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = η x ^ 2 * s * |C| + 2 * |η x| * s * |Tη| +
          (2 * p - 2) * η x ^ 2 * t * |Tw| := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg (η x)), abs_of_nonneg hs,
          abs_of_nonneg ht, abs_of_nonneg hq, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ η x ^ 2 * s * (a * y) + 2 * |η x| * s * (e * a * w x) +
          (2 * p - 2) * η x ^ 2 * t * (z * a * w x) := by gcongr
      _ = η x ^ 2 * s * (a * y) + 2 * |η x| * s * (e * a * w x) +
          (2 * p - 2) * η x ^ 2 * (t * w x) * (z * a) := by ring
      _ = _ := by rw [htw, sq_abs]; ring
  have hcrossabs : |2 * η x * w x ^ (2 * p - 1) *
      g.inner x (D.gradient η x) (D.gradient w x)| ≤
      s * (2 * |η x| * w x * e * y) := by
    rw [hsw]
    simp only [abs_mul, abs_of_nonneg hs, abs_of_pos hwpos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * |η x| * (s * w x) * (e * y) := by gcongr
      _ = _ := by ring
  have hSV := D.sum_inner_connection_regularized_power hVs hηs hε p x
  change SV = η x ^ 2 * s * A + (2 * p - 2) * η x ^ 2 * s * W +
    2 * η x * w x ^ (2 * p - 1) * g.inner x (D.gradient η x) (D.gradient w x) at hSV
  have habsorb := mul_le_mul_of_nonneg_left
    (power_test_absorption hp |η x| (w x) e y z a) hs
  rw [sq_abs, hy2, hz2, he2, ha2] at habsorb
  rw [sq_abs] at hSXabs
  have hnegSX := neg_le_abs SX
  have hnegcross := neg_le_abs (2 * η x * w x ^ (2 * p - 1) *
    g.inner x (D.gradient η x) (D.gradient w x))
  have hweighted := mul_le_mul_of_nonneg_left hWA (mul_nonneg (sq_nonneg (η x)) hs)
  change (p - 1 / 2) * (η x ^ 2 * s * W) ≤ SV + SX +
    5 * ((w x ^ p) ^ 2 * E) + (p + 1) * (η x ^ 2 * s * B)
  nlinarith only [hSV, habsorb, hSXabs, hcrossabs, hnegSX, hnegcross,
    hweighted, congrArg (fun q : ℝ => q * E) hsp]

private theorem metric_inner_add_self_le (x : EuclideanSpace ℝ (Fin n))
    (u v : TangentSpace (𝓡 n) x) :
    g.inner x (u + v) (u + v) ≤ 2 * g.inner x u u + 2 * g.inner x v v := by
  have h := metric_inner_self_nonneg (g := g) x (u - v)
  simp only [map_sub, sub_apply] at h
  simp only [map_add, add_apply]
  rw [g.symm x v u] at h ⊢
  linarith

private theorem ricci_smul_right (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (u v : TangentSpace (𝓡 n) x) (c : ℝ) :
    D.ricci x u (c • v) = c * D.ricci x u v := by
  simp only [ricci, curvatureTensor, map_smul, smul_eq_mul, Finset.mul_sum]

theorem regularized_gradient_sub_power_caccioppoli (D : LeviCivitaData g)
    {f η : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {ε p κ L : ℝ}
    (hε : 0 < ε) (hp : 1 ≤ p) (hκ : 0 ≤ κ) (hL : 0 ≤ L)
    (hharm : ∀ x ∈ tsupport η, D.laplacian f =ᶠ[𝓝 x] fun _ => 0)
    (hRic : ∀ x ∈ tsupport η,
      -κ * (g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)
        ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x) + ε) ≤
        D.ricci x (D.gradient f x)
          ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x))
    (hconn : ∀ x ∈ tsupport η,
      (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
        (D.connection X x (g.orthonormalBasis x i))) ≤
          L * (g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)
            ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x) + ε)) :
    let w := fun x => Real.sqrt
      (g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)
        ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x) + ε)
    (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
      (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
      22 * p ^ 2 * ((∫ x, (w x ^ p) ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) +
        (κ + L) * ∫ x, η x ^ 2 * (w x ^ p) ^ 2 ∂g.volumeMeasure) := by
  let V := fun y => (show EuclideanSpace ℝ (Fin n) from D.gradient f y) - X y
  let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
  let Z := fun y => (η y ^ 2 * w y ^ (2 * p - 2)) • V y
  let F := fun x => η x ^ 2 * w x ^ (2 * p - 2) *
    g.inner x (D.gradient w x) (D.gradient w x)
  let G := fun x => (w x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)
  let M := fun x => η x ^ 2 * (w x ^ p) ^ 2
  let SV := fun x => ∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
    (D.connection Z x (g.orthonormalBasis x i))
  let SX := fun x => ∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
    (D.connection Z x (g.orthonormalBasis x i))
  let R := fun x => D.ricci x (D.gradient f x) (Z x)
  have hfs := contMDiff_iff_contDiff.mpr hf
  have hV : ContDiff ℝ ∞ V :=
    (contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hfs)).sub hX
  have hVs := contMDiff_vectorSpace_iff_contDiff.mpr hV
  have hXs := contMDiff_vectorSpace_iff_contDiff.mpr hX
  have hηs := contMDiff_iff_contDiff.mpr hη
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := contMDiff_regularized_vector_norm hVs hε
  have hwpos (x : EuclideanSpace ℝ (Fin n)) : 0 < w x :=
    regularized_vector_norm_pos (g := g) V hε x
  have hw2 (x : EuclideanSpace ℝ (Fin n)) : w x ^ 2 = g.inner x (V x) (V x) + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hwpos x)).le
  have hwp := contMDiff_rpow_of_pos hw hwpos p
  have hwq := contMDiff_rpow_of_pos hw hwpos (2 * p - 2)
  have hφ := (hηs.pow 2).mul hwq
  have hZ : ContDiff ℝ ∞ Z := (contMDiff_iff_contDiff.mp hφ).smul hV
  have hZs := contMDiff_vectorSpace_iff_contDiff.mpr hZ
  have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
    rw [show (fun x => η x ^ 2) = η * η by ext x; simp [pow_two]]
    exact hηc.mul_right
  have hZc : HasCompactSupport Z := hη2c.mul_right.smul_right
  have hZη : tsupport Z ⊆ tsupport η := by
    exact (tsupport_smul_subset_left _ _).trans
      (tsupport_mul_subset_left.trans (by simpa only [pow_two] using tsupport_mul_subset_left))
  have hhZ := fun x hx => hharm x (hZη hx)
  have hFi : Integrable F g.volumeMeasure :=
    (hφ.continuous.mul (D.contMDiff_inner_gradient hw hw).continuous).integrable_of_hasCompactSupport
      hη2c.mul_right.mul_right
  have hGi : Integrable G g.volumeMeasure :=
    ((hwp.pow 2).continuous.mul (D.contMDiff_inner_gradient hηs hηs).continuous).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_left
  have hMi : Integrable M g.volumeMeasure :=
    ((hηs.pow 2).continuous.mul (hwp.pow 2).continuous).integrable_of_hasCompactSupport
      hη2c.mul_right
  have hSVi : Integrable SV g.volumeMeasure := D.integrable_inner_connection hVs hZs hZc
  have hSXi : Integrable SX g.volumeMeasure := D.integrable_inner_connection hXs hZs hZc
  have hRi : Integrable R g.volumeMeasure := D.integrable_ricci_harmonic_gradient hf hZ hZc hhZ
  have hFn (x) : 0 ≤ F x := mul_nonneg
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hwpos x).le _)) (metric_inner_self_nonneg x _)
  have hGn (x) : 0 ≤ G x := mul_nonneg (sq_nonneg _) (metric_inner_self_nonneg x _)
  have hMn (x) : 0 ≤ M x := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hF0 : 0 ≤ ∫ x, F x ∂g.volumeMeasure := integral_nonneg hFn
  have hG0 : 0 ≤ ∫ x, G x ∂g.volumeMeasure := integral_nonneg hGn
  have hM0 : 0 ≤ ∫ x, M x ∂g.volumeMeasure := integral_nonneg hMn
  have hB (x) : η x ^ 2 * w x ^ (2 * p - 2) *
      (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
        (D.connection X x (g.orthonormalBasis x i))) ≤ L * M x := by
    by_cases hx : x ∈ tsupport η
    · have h := mul_le_mul_of_nonneg_left (hconn x hx)
        (mul_nonneg (sq_nonneg (η x)) (Real.rpow_nonneg (hwpos x).le (2 * p - 2)))
      change _ ≤ (η x ^ 2 * w x ^ (2 * p - 2)) * (L * (g.inner x (V x) (V x) + ε)) at h
      rw [← hw2] at h
      have heq := rpow_weight_sq (hwpos x) p
      dsimp only [M]
      nlinarith only [h, congrArg (fun z : ℝ => L * η x ^ 2 * z) heq]
    · simp [M, image_eq_zero_of_notMem_tsupport hx]
  have hpoint (x) : (p - 1 / 2) * F x ≤
      SV x + SX x + 5 * G x + ((p + 1) * L) * M x := by
    have h := D.regularized_power_test_lower (X := X) hV hη hε hp x
    have hb := mul_le_mul_of_nonneg_left (hB x) (show 0 ≤ p + 1 by linarith)
    change (p - 1 / 2) * F x ≤ SV x + SX x + 5 * G x + _ at h
    linarith
  have hi := integral_mono (hFi.const_mul (p - 1 / 2))
    (((hSVi.add hSXi).add (hGi.const_mul 5)).add (hMi.const_mul ((p + 1) * L))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun x => SV x + SX x + 5 * G x)
      ((hSVi.add hSXi).add (hGi.const_mul 5)) (hMi.const_mul ((p + 1) * L)),
    integral_add (f := fun x => SV x + SX x) (hSVi.add hSXi) (hGi.const_mul 5),
    integral_add hSVi hSXi,
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  have hweak := D.integral_inner_connection_gradient_sub hf hX hZ hZc hhZ
  change (∫ x, SV x ∂g.volumeMeasure) = -(∫ x, R x ∂g.volumeMeasure) -
    ∫ x, SX x ∂g.volumeMeasure at hweak
  have hRicLower : -κ * (∫ x, M x ∂g.volumeMeasure) ≤ ∫ x, R x ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply integral_mono (hMi.const_mul (-κ)) hRi
    intro x
    by_cases hx : x ∈ tsupport η
    · have h := mul_le_mul_of_nonneg_left (hRic x hx)
        (mul_nonneg (sq_nonneg (η x)) (Real.rpow_nonneg (hwpos x).le (2 * p - 2)))
      change (η x ^ 2 * w x ^ (2 * p - 2)) * (-κ * (g.inner x (V x) (V x) + ε)) ≤ _ at h
      rw [← hw2] at h
      have heq := rpow_weight_sq (hwpos x) p
      change -κ * (η x ^ 2 * (w x ^ p) ^ 2) ≤ D.ricci x (D.gradient f x)
        ((η x ^ 2 * w x ^ (2 * p - 2)) • (show TangentSpace (𝓡 n) x from V x))
      rw [ricci_smul_right]
      nlinarith only [h, congrArg (fun z : ℝ => κ * η x ^ 2 * z) heq]
    · change -κ * (η x ^ 2 * (w x ^ p) ^ 2) ≤ D.ricci x (D.gradient f x)
        ((η x ^ 2 * w x ^ (2 * p - 2)) • (show TangentSpace (𝓡 n) x from V x))
      rw [ricci_smul_right]
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hweighted : (p - 1 / 2) * (∫ x, F x ∂g.volumeMeasure) ≤
      5 * (∫ x, G x ∂g.volumeMeasure) + (κ + (p + 1) * L) *
        ∫ x, M x ∂g.volumeMeasure := by linarith
  have hFbound : (∫ x, F x ∂g.volumeMeasure) ≤
      10 * (∫ x, G x ∂g.volumeMeasure) + 4 * (κ + L) *
        ∫ x, M x ∂g.volumeMeasure := by
    apply (mul_le_mul_iff_right₀ (show 0 < p - 1 / 2 by linarith)).mp
    have hkM := mul_nonneg hκ hM0
    have hlM := mul_nonneg hL hM0
    nlinarith only [hweighted, hkM,
      mul_nonneg (sub_nonneg.mpr hp) hG0,
      mul_nonneg (sub_nonneg.mpr hp) hkM,
      mul_nonneg (sub_nonneg.mpr hp) hlM]
  have hcutpoint (x) : g.inner x (D.gradient (fun y => η y * w y ^ p) x)
      (D.gradient (fun y => η y * w y ^ p) x) ≤ 2 * G x + 2 * p ^ 2 * F x := by
    rw [D.gradient_mul ((hηs x).mdifferentiableAt (by simp))
      ((hwp x).mdifferentiableAt (by simp)), D.gradient_rpow_of_pos hw hwpos]
    have h := metric_inner_add_self_le (g := g) x
      (η x • ((p * w x ^ (p - 1)) • D.gradient w x))
      ((w x ^ p) • D.gradient η x)
    have hpow : (w x ^ (p - 1)) ^ 2 = w x ^ (2 * p - 2) := by
      rw [← Real.rpow_mul_natCast (hwpos x).le]
      congr 1
      ring
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    dsimp only [F, G]
    nlinarith only [h, congrArg (fun z : ℝ =>
      2 * η x ^ 2 * p ^ 2 * z * g.inner x (D.gradient w x) (D.gradient w x)) hpow]
  have hcuti := D.integrable_inner_gradient (hηs.mul hwp) (hηs.mul hwp) hηc.mul_right
  have hcut := integral_mono hcuti ((hGi.const_mul 2).add (hFi.const_mul (2 * p ^ 2))) hcutpoint
  simp only [Pi.add_apply] at hcut
  rw [integral_add (hGi.const_mul 2) (hFi.const_mul (2 * p ^ 2)),
    integral_const_mul, integral_const_mul] at hcut
  change (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
    (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
      2 * (∫ x, G x ∂g.volumeMeasure) + 2 * p ^ 2 * ∫ x, F x ∂g.volumeMeasure at hcut
  have hmul := mul_le_mul_of_nonneg_left hFbound (show 0 ≤ 2 * p ^ 2 by positivity)
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hKM := mul_nonneg (add_nonneg hκ hL) hM0
  change (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
    (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
    22 * p ^ 2 * ((∫ x, G x ∂g.volumeMeasure) + (κ + L) * ∫ x, M x ∂g.volumeMeasure)
  nlinarith only [hcut, hmul, mul_nonneg (sub_nonneg.mpr hp2) hG0,
    mul_nonneg (sq_nonneg p) hKM]

end PoincareConjecture.LeviCivitaData
