import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedCalculus
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SmoothRelabeling










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold
open scoped Manifold ContDiff Bundle BigOperators

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem hasDerivAt_embeddedCurvatureJet_spatial
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let de : TangentSpace (𝓡 n) (c x t) →L[ℝ] W :=
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
    HasDerivAt (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t)
      (m63CurvatureJet F c i t y) : W))
      (curveSpeed F c t x • (de (m63CurvatureJet F c (i + 1) t x) +
        coordinateHessian (F.connection t) e (c x t)
          (spatialUnitTangent F c t x) (m63CurvatureJet F c i t x))) x := by
  classical
  dsimp only
  let p := c x t
  let D := F.connection t
  let v := curveSpeed F c t x
  let S := spatialUnitTangent F c t x
  let J := m63CurvatureJet F c i t x
  let J1 := m63CurvatureJet F c (i + 1) t x
  let de : TangentSpace (𝓡 n) p →L[ℝ] W := mfderiv (𝓡 n) 𝓘(ℝ, W) e p
  have hv : v ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hX : curveVelocity (fun y => c y t) x = v • S := by
    dsimp only [S, spatialUnitTangent]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDX : rampHorizontalCovariantDerivative D (fun y => c y t)
      (fun y => m63CurvatureJet F c i t y) x = v • J1 := by
    change _ = v • (v⁻¹ • _)
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hE : coordinateHessian D e p (v • S) J = v • coordinateHessian D e p S J := by
    ext k
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q k) :=
      (EuclideanSpace.proj k).contDiff.contMDiff.comp he
    obtain ⟨L, hL⟩ := (M04.isSmoothCovariantTensor_hessian D hf).1 p
    have hu (Y : TangentSpace (𝓡 n) p) : Function.update ![S, J] 0 Y = ![Y, J] := by
      ext j
      fin_cases j <;> simp [Function.update]
    change D.hessian (fun q => e q k) p (v • S) J =
      v * D.hessian (fun q => e q k) p S J
    simpa [hu, ← hL, smul_eq_mul] using L.map_update_smul ![S, J] 0 v S
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hd := hasDerivAt_embedding_pushforward D he hcurve
    (fun y => m63CurvatureJet F c i t y) (curvatureJet_mdifferentiable F c hc ht i x)
  change HasDerivAt (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t)
    (m63CurvatureJet F c i t y) : W))
    (coordinateHessian D e p (curveVelocity (fun y => c y t) x) J +
      de (rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => m63CurvatureJet F c i t y) x)) x at hd
  rw [hX, hDX, hE, map_smul] at hd
  convert! hd using 1
  dsimp only [v, D, p, S, J, J1, de]
  simp only [smul_add]
  ext k
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring




theorem embeddedCurvatureJet_second_spatial_derivative_bound
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    {E1 E2 E3 : ℝ} (_hE1 : 0 ≤ E1) (_hE2 : 0 ≤ E2) (_hE3 : 0 ≤ E3)
    (hde : ∀ V : TangentSpace (𝓡 n) (c x t),
      Norm.norm (E := W) (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) V) ≤
        E1 * (F.metric t).tangentNorm (c x t) V)
    (hE : ∀ V Z : TangentSpace (𝓡 n) (c x t),
      ‖coordinateHessian (F.connection t) e (c x t) V Z‖ ≤
        E2 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Z)
    (hT : ∀ V Y Z : TangentSpace (𝓡 n) (c x t),
      ‖WithLp.toLp 2 (fun k : ι => (F.connection t).covariantTensorDerivative
          (fun q w => (F.connection t).hessian (fun z => e z k) q (w 0) (w 1))
          (c x t) ![V, Y, Z])‖ ≤
        E3 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Y *
          (F.metric t).tangentNorm (c x t) Z) :
    let eta : ℝ → W := fun y =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t) (m63CurvatureJet F c i t y)
    let v := curveSpeed F c t x
    let k := m62Curvature F c t x
    let hj := fun j => (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c j t x)
    ‖deriv (deriv eta) x‖ ≤
      |deriv (curveSpeed F c t) x| * (E2 * hj i + E1 * hj (i + 1)) +
        v ^ 2 * (E3 * hj i + E2 * k * hj i + 2 * E2 * hj (i + 1) +
          E1 * hj (i + 2)) := by
  classical
  dsimp only
  let D := F.connection t
  let p := c x t
  let v := curveSpeed F c t x
  let vx := deriv (curveSpeed F c t) x
  let S := spatialUnitTangent F c t
  let H := m62CurvatureVector F c t
  let J := m63CurvatureJet F c i t
  let J1 := m63CurvatureJet F c (i + 1) t
  let J2 := m63CurvatureJet F c (i + 2) t x
  let de (y : ℝ) : TangentSpace (𝓡 n) (c y t) →L[ℝ] W :=
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t)
  let E (y : ℝ) := coordinateHessian D e (c y t)
  let T : ι → CovariantTensorEvaluation n M 2 :=
    fun k q w => D.hessian (fun z => e z k) q (w 0) (w 1)
  let T0 := WithLp.toLp 2 (fun k => D.covariantTensorDerivative (T k) p ![S x, S x, J x])
  let eta : ℝ → W := fun y => de y (J y)
  let C : ℝ → W := fun y => de y (J1 y) + E y (S y) (J y)
  let C2 := de x J2 + (2 : ℝ) • E x (S x) (J1 x) + E x (H x) (J x) + T0
  let hj := fun j => (F.metric t).tangentNorm p (m63CurvatureJet F c j t x)
  let k := m62Curvature F c t x
  have hv : v ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hX : curveVelocity (fun y => c y t) x = v • S x := by
    dsimp only [S, spatialUnitTangent]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDS : rampHorizontalCovariantDerivative D (fun y => c y t) S x = v • H x := by
    dsimp only [H, m62CurvatureVector, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDJ : rampHorizontalCovariantDerivative D (fun y => c y t) J x = v • J1 x := by
    change _ = v • (v⁻¹ • _)
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hTensor (j : ι) : IsSmoothCovariantTensor (T j) :=
    M04.isSmoothCovariantTensor_hessian D ((EuclideanSpace.proj j).contDiff.contMDiff.comp he)
  have hEleft (Y Z : TangentSpace (𝓡 n) p) : E x (v • Y) Z = v • E x Y Z := by
    ext j
    obtain ⟨L, hL⟩ := (hTensor j).1 p
    have hu (A : TangentSpace (𝓡 n) p) : Function.update ![Y, Z] 0 A = ![A, Z] := by
      ext q
      fin_cases q <;> simp [Function.update]
    change T j p ![v • Y, Z] = v * T j p ![Y, Z]
    simpa only [hu, ← hL, smul_eq_mul] using L.map_update_smul ![Y, Z] 0 v Y
  have hEright (Y Z : TangentSpace (𝓡 n) p) : E x Y (v • Z) = v • E x Y Z := by
    ext j
    obtain ⟨L, hL⟩ := (hTensor j).1 p
    have hu (A : TangentSpace (𝓡 n) p) : Function.update ![Y, Z] 1 A = ![Y, A] := by
      ext q
      fin_cases q <;> simp [Function.update]
    change T j p ![Y, v • Z] = v * T j p ![Y, Z]
    simpa only [hu, ← hL, smul_eq_mul] using L.map_update_smul ![Y, Z] 1 v Z
  have hT0 : WithLp.toLp 2 (fun j => D.covariantTensorDerivative (T j) p
      ![v • S x, S x, J x]) = v • T0 := by
    ext j
    obtain ⟨L, hL⟩ :=
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D (hTensor j)).1 p
    have hu (A : TangentSpace (𝓡 n) p) : Function.update ![S x, S x, J x] 0 A =
        ![A, S x, J x] := by
      ext q
      fin_cases q <;> simp [Function.update]
    change D.covariantTensorDerivative (T j) p ![v • S x, S x, J x] =
      v * D.covariantTensorDerivative (T j) p ![S x, S x, J x]
    simpa only [hu, ← hL, smul_eq_mul] using L.map_update_smul ![S x, S x, J x] 0 v (S x)
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hJ1 := hasDerivAt_embeddedCurvatureJet_spatial F c hc he (i + 1) ht x
  change HasDerivAt (fun y => de y (J1 y))
    (v • (de x J2 + E x (S x) (J1 x))) x at hJ1
  have hEder := hasDerivAt_coordinateHessian_pullback D he hcurve S J
    (unitTangent_mdifferentiable F c hc ht x)
    (curvatureJet_mdifferentiable F c hc ht i x)
  change HasDerivAt (fun y => E y (S y) (J y))
    (WithLp.toLp 2 (fun j => D.covariantTensorDerivative (T j) p
        ![curveVelocity (fun y => c y t) x, S x, J x]) +
      E x (rampHorizontalCovariantDerivative D (fun y => c y t) S x) (J x) +
      E x (S x) (rampHorizontalCovariantDerivative D (fun y => c y t) J x)) x at hEder
  rw [hX, hDS, hDJ, hT0, hEleft, hEright] at hEder
  have hC : HasDerivAt C (v • C2) x := by
    apply (hJ1.add hEder).congr_deriv
    dsimp only [C2]
    simp only [smul_add, smul_smul]
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hspeed : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hfirst : deriv eta = fun y => curveSpeed F c t y • C y := by
    funext y
    exact (hasDerivAt_embeddedCurvatureJet_spatial F c hc he i ht y).deriv
  have hsecond : deriv (deriv eta) x = v ^ 2 • C2 + vx • C x := by
    rw [hfirst]
    have hd := ((hspeed.differentiable (by simp) x).hasDerivAt).fun_smul hC
    simpa only [Pi.smul_apply, v, vx, smul_smul, pow_two] using hd.deriv
  have hS : (F.metric t).tangentNorm p (S x) = 1 :=
    unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hH : (F.metric t).tangentNorm p (H x) = k := rfl
  have hEJ : ‖E x (S x) (J x)‖ ≤ E2 * hj i := by
    have hh := hE (S x) (J x)
    change ‖E x (S x) (J x)‖ ≤ E2 * (F.metric t).tangentNorm p (S x) * hj i at hh
    simpa only [hS, mul_one] using hh
  have hEJ1 : ‖E x (S x) (J1 x)‖ ≤ E2 * hj (i + 1) := by
    have hh := hE (S x) (J1 x)
    change ‖E x (S x) (J1 x)‖ ≤
      E2 * (F.metric t).tangentNorm p (S x) * hj (i + 1) at hh
    simpa only [hS, mul_one] using hh
  have hEHJ : ‖E x (H x) (J x)‖ ≤ E2 * k * hj i := by
    have hh := hE (H x) (J x)
    change ‖E x (H x) (J x)‖ ≤ E2 * (F.metric t).tangentNorm p (H x) * hj i at hh
    simpa only [hH] using hh
  have hTbound : ‖T0‖ ≤ E3 * hj i := by
    have hh := hT (S x) (S x) (J x)
    change ‖T0‖ ≤ E3 * (F.metric t).tangentNorm p (S x) *
      (F.metric t).tangentNorm p (S x) * hj i at hh
    simpa only [hS, mul_one] using hh
  have hCbound : ‖C x‖ ≤ E2 * hj i + E1 * hj (i + 1) := by
    calc
      ‖C x‖ ≤ ‖de x (J1 x)‖ + ‖E x (S x) (J x)‖ := norm_add_le _ _
      _ ≤ E1 * hj (i + 1) + E2 * hj i := add_le_add (hde (J1 x)) hEJ
      _ = _ := add_comm _ _
  have htwo : ‖(2 : ℝ) • E x (S x) (J1 x)‖ ≤ 2 * E2 * hj (i + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hEJ1 (by norm_num : (0 : ℝ) ≤ 2)
  have hC2bound : ‖C2‖ ≤
      E3 * hj i + E2 * k * hj i + 2 * E2 * hj (i + 1) + E1 * hj (i + 2) := by
    have hnorm : ‖C2‖ ≤
        ‖de x J2‖ + ‖(2 : ℝ) • E x (S x) (J1 x)‖ + ‖E x (H x) (J x)‖ + ‖T0‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))) (le_refl _))
    have hsum := hnorm.trans (add_le_add (add_le_add (add_le_add (hde J2) htwo) hEHJ) hTbound)
    change ‖C2‖ ≤ E1 * hj (i + 2) + 2 * E2 * hj (i + 1) + E2 * k * hj i + E3 * hj i at hsum
    linarith only [hsum]
  change ‖deriv (deriv eta) x‖ ≤ |vx| * (E2 * hj i + E1 * hj (i + 1)) +
    v ^ 2 * (E3 * hj i + E2 * k * hj i + 2 * E2 * hj (i + 1) + E1 * hj (i + 2))
  rw [hsecond]
  calc
    ‖v ^ 2 • C2 + vx • C x‖ ≤ ‖v ^ 2 • C2‖ + ‖vx • C x‖ := norm_add_le _ _
    _ = v ^ 2 * ‖C2‖ + |vx| * ‖C x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg v)]
    _ ≤ v ^ 2 * (E3 * hj i + E2 * k * hj i + 2 * E2 * hj (i + 1) + E1 * hj (i + 2)) +
        |vx| * (E2 * hj i + E1 * hj (i + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hC2bound (sq_nonneg v))
        (mul_le_mul_of_nonneg_left hCbound (abs_nonneg vx))
    _ = _ := add_comm _ _

end PoincareConjecture.M63
