import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedCalculus
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureError
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

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

theorem hasDerivAt_embeddedCurvature_spatial
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let de : TangentSpace (𝓡 n) (c x t) →L[ℝ] W :=
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
    HasDerivAt (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t)
      (m62CurvatureVector F c t y) : W))
      (curveSpeed F c t x • (de (m63CurvatureJet F c 1 t x) +
        coordinateHessian (F.connection t) e (c x t)
          (spatialUnitTangent F c t x) (m62CurvatureVector F c t x))) x := by
  classical
  dsimp only
  let p := c x t
  let D := F.connection t
  let v := curveSpeed F c t x
  let S := spatialUnitTangent F c t x
  let H := m62CurvatureVector F c t x
  let B := m63CurvatureJet F c 1 t x
  let de : TangentSpace (𝓡 n) p →L[ℝ] W := mfderiv (𝓡 n) 𝓘(ℝ, W) e p
  have hv : v ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hX : curveVelocity (fun y => c y t) x = v • S := by
    dsimp only [S, spatialUnitTangent]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDX : rampHorizontalCovariantDerivative D (fun y => c y t)
      (fun y => m62CurvatureVector F c t y) x = v • B := by
    dsimp only [B, m63CurvatureJet, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hE : coordinateHessian D e p (v • S) H = v • coordinateHessian D e p S H := by
    ext i
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q i) :=
      (EuclideanSpace.proj i).contDiff.contMDiff.comp he
    obtain ⟨L, hL⟩ := (M04.isSmoothCovariantTensor_hessian D hf).1 p
    have hu (Y : TangentSpace (𝓡 n) p) : Function.update ![S, H] 0 Y = ![Y, H] := by
      ext j
      fin_cases j <;> simp [Function.update]
    change D.hessian (fun q => e q i) p (v • S) H =
      v * D.hessian (fun q => e q i) p S H
    simpa [hu, ← hL, smul_eq_mul] using L.map_update_smul ![S, H] 0 v S
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hY := curvatureJet_mdifferentiable F c hc ht 0 x
  have hd := hasDerivAt_embedding_pushforward D he hcurve
    (fun y => m62CurvatureVector F c t y) hY
  change HasDerivAt (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t)
    (m62CurvatureVector F c t y) : W))
    (coordinateHessian D e p (curveVelocity (fun y => c y t) x) H +
      de (rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => m62CurvatureVector F c t y) x)) x at hd
  rw [hX, hDX, hE, map_smul] at hd
  convert! hd using 1
  dsimp only [v, D, p, S, H, B, de]
  simp only [smul_add]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_embeddedCurvature_time
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let p := c x t
    let v := curveSpeed F c t x
    let S := spatialUnitTangent F c t x
    let H := m62CurvatureVector F c t x
    let B := m63CurvatureJet F c 1 t x
    let de : TangentSpace (𝓡 n) p →L[ℝ] W := mfderiv (𝓡 n) 𝓘(ℝ, W) e p
    let T : ι → CovariantTensorEvaluation n M 2 :=
      fun i q w => D.hessian (fun z => e z i) q (w 0) (w 1)
    let Hhat : ℝ → ℝ → W := fun r y =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r) (m62CurvatureVector F c r y)
    let Q := rampHorizontalCovariantDerivative D (fun r => c x r)
      (fun r => m62CurvatureVector F c r x) t - m63CurvatureJet F c 2 t x
    HasDerivAt (fun r => Hhat r x)
      ((v ^ 2)⁻¹ • iteratedDeriv 2 (Hhat t) x + de Q -
        (deriv (curveSpeed F c t) x / v ^ 3) • deriv (Hhat t) x -
        (2 : ℝ) • coordinateHessian D e p S B -
        WithLp.toLp 2 (fun i => D.covariantTensorDerivative (T i) p ![S, S, H])) t := by
  classical
  dsimp only
  let D := F.connection t
  let p := c x t
  let v := curveSpeed F c t x
  let vx := deriv (curveSpeed F c t) x
  let S := spatialUnitTangent F c t
  let H := m62CurvatureVector F c t
  let B := m63CurvatureJet F c 1 t
  let H2 := m63CurvatureJet F c 2 t x
  let de (y : ℝ) : TangentSpace (𝓡 n) (c y t) →L[ℝ] W :=
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t)
  let E (y : ℝ) := coordinateHessian D e (c y t)
  let T : ι → CovariantTensorEvaluation n M 2 :=
    fun i q w => D.hessian (fun z => e z i) q (w 0) (w 1)
  let J := WithLp.toLp 2 (fun i => D.covariantTensorDerivative (T i) p ![S x, S x, H x])
  let Hhat : ℝ → ℝ → W := fun r y =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r) (m62CurvatureVector F c r y)
  let DtH := rampHorizontalCovariantDerivative D (fun r => c x r)
    (fun r => m62CurvatureVector F c r x) t
  let C : ℝ → W := fun y => de y (B y) + E y (S y) (H y)
  have hv : v ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hX : curveVelocity (fun y => c y t) x = v • S x := by
    dsimp only [S, spatialUnitTangent]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDS : rampHorizontalCovariantDerivative D (fun y => c y t) S x = v • H x := by
    dsimp only [H, m62CurvatureVector, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDH : rampHorizontalCovariantDerivative D (fun y => c y t) H x = v • B x := by
    dsimp only [B, m63CurvatureJet, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDB : rampHorizontalCovariantDerivative D (fun y => c y t) B x = v • H2 := by
    dsimp only [H2, m63CurvatureJet, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
    rfl
  have hT (i : ι) : IsSmoothCovariantTensor (T i) :=
    M04.isSmoothCovariantTensor_hessian D ((EuclideanSpace.proj i).contDiff.contMDiff.comp he)
  have hEleft (Y Z : TangentSpace (𝓡 n) p) : E x (v • Y) Z = v • E x Y Z := by
    ext i
    obtain ⟨L, hL⟩ := (hT i).1 p
    have hu (A : TangentSpace (𝓡 n) p) : Function.update ![Y, Z] 0 A = ![A, Z] := by
      ext j
      fin_cases j <;> simp [Function.update]
    change T i p ![v • Y, Z] = v * T i p ![Y, Z]
    simpa only [hu, ← hL, smul_eq_mul] using L.map_update_smul ![Y, Z] 0 v Y
  have hEright (Y Z : TangentSpace (𝓡 n) p) : E x Y (v • Z) = v • E x Y Z := by
    ext i
    obtain ⟨L, hL⟩ := (hT i).1 p
    have hu (A : TangentSpace (𝓡 n) p) : Function.update ![Y, Z] 1 A = ![Y, A] := by
      ext j
      fin_cases j <;> simp [Function.update]
    change T i p ![Y, v • Z] = v * T i p ![Y, Z]
    simpa only [hu, ← hL, smul_eq_mul] using L.map_update_smul ![Y, Z] 1 v Z
  have hJ : WithLp.toLp 2 (fun i => D.covariantTensorDerivative (T i) p
      ![v • S x, S x, H x]) = v • J := by
    ext i
    obtain ⟨L, hL⟩ := (M04.isSmoothCovariantTensor_covariantTensorDerivative D (hT i)).1 p
    have hu (A : TangentSpace (𝓡 n) p) : Function.update ![S x, S x, H x] 0 A =
        ![A, S x, H x] := by
      ext j
      fin_cases j <;> simp [Function.update]
    change D.covariantTensorDerivative (T i) p ![v • S x, S x, H x] =
      v * D.covariantTensorDerivative (T i) p ![S x, S x, H x]
    simpa only [hu, ← hL, smul_eq_mul] using L.map_update_smul ![S x, S x, H x] 0 v (S x)
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have htime : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun r : ℝ => (x, r)) t :=
    (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hcurvet : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun r => c x r) t :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp t htime
  have hHtime := (((curvatureJet_joint_contMDiff F c hc 0).contMDiffAt
    (hopen.mem_nhds hmem)).comp t htime).mdifferentiableAt (by simp)
  have hdt := hasDerivAt_embedding_pushforward D he hcurvet
    (fun r => m62CurvatureVector F c r x) hHtime
  rw [hc.equation t ht x] at hdt
  have hB := hasDerivAt_embedding_pushforward D he hcurve B
    (curvatureJet_mdifferentiable F c hc ht 1 x)
  change HasDerivAt (fun y => de y (B y))
    (E x (curveVelocity (fun y => c y t) x) (B x) +
      de x (rampHorizontalCovariantDerivative D (fun y => c y t) B x)) x at hB
  rw [hX, hDB, hEleft, map_smul] at hB
  have hE := hasDerivAt_coordinateHessian_pullback D he hcurve S H
    (unitTangent_mdifferentiable F c hc ht x)
    (curvatureJet_mdifferentiable F c hc ht 0 x)
  change HasDerivAt (fun y => E y (S y) (H y))
    (WithLp.toLp 2 (fun i => D.covariantTensorDerivative (T i) p
        ![curveVelocity (fun y => c y t) x, S x, H x]) +
      E x (rampHorizontalCovariantDerivative D (fun y => c y t) S x) (H x) +
      E x (S x) (rampHorizontalCovariantDerivative D (fun y => c y t) H x)) x at hE
  rw [hX, hDS, hDH, hJ, hEleft, hEright] at hE
  have hC : HasDerivAt C
      (v • (de x H2 + (2 : ℝ) • E x (S x) (B x) + E x (H x) (H x) + J)) x := by
    apply (hB.add hE).congr_deriv
    simp only [smul_add, smul_smul]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hspeed : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hfirst : deriv (Hhat t) = fun y => curveSpeed F c t y • C y := by
    funext y
    exact (hasDerivAt_embeddedCurvature_spatial F c hc he ht y).deriv
  have hsecond : iteratedDeriv 2 (Hhat t) x =
      v ^ 2 • (de x H2 + (2 : ℝ) • E x (S x) (B x) + E x (H x) (H x) + J) +
        vx • C x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst]
    have hd := ((hspeed.differentiable (by simp) x).hasDerivAt).fun_smul hC
    simpa only [Pi.smul_apply, v, vx, smul_smul, pow_two] using hd.deriv
  change HasDerivAt (fun r => Hhat r x)
    ((v ^ 2)⁻¹ • iteratedDeriv 2 (Hhat t) x + de x (DtH - H2) -
      (vx / v ^ 3) • deriv (Hhat t) x - (2 : ℝ) • E x (S x) (B x) - J) t
  apply hdt.congr_deriv
  change E x (H x) (H x) + de x DtH = _
  rw [hsecond, hfirst, map_sub]
  simp only [smul_add, smul_smul]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hv]
  ring

theorem embeddedCurvature_derivative_remainder_bounds
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    {E1 E2 E3 : ℝ} (hE1 : 0 ≤ E1) (_hE2 : 0 ≤ E2) (_hE3 : 0 ≤ E3)
    (hde : ∀ V : TangentSpace (𝓡 n) (c x t),
      Norm.norm (E := W) (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) V) ≤
        E1 * (F.metric t).tangentNorm (c x t) V)
    (hE : ∀ V Z : TangentSpace (𝓡 n) (c x t),
      ‖coordinateHessian (F.connection t) e (c x t) V Z‖ ≤
        E2 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Z)
    (hJ : ∀ V Y Z : TangentSpace (𝓡 n) (c x t),
      ‖WithLp.toLp 2 (fun i : ι => (F.connection t).covariantTensorDerivative
          (fun q w => (F.connection t).hessian (fun z => e z i) q (w 0) (w 1))
          (c x t) ![V, Y, Z])‖ ≤
        E3 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Y *
          (F.metric t).tangentNorm (c x t) Z) :
    let Hhat : ℝ → ℝ → W := fun r y =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r) (m62CurvatureVector F c r y)
    let v := curveSpeed F c t x
    let k := m62Curvature F c t x
    let u := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x)
    ‖deriv (Hhat t) x‖ ≤ v * (E1 * u + E2 * k) ∧
      ‖deriv (fun r => Hhat r x) t - (v ^ 2)⁻¹ • iteratedDeriv 2 (Hhat t) x‖ ≤
        E1 * (2 * k ^ 3 + (K0 + 4 * K2) * k + 4 * K1 + 2 * k * u) +
          (|deriv (curveSpeed F c t) x| / v ^ 2) * (E1 * u + E2 * k) +
          2 * E2 * u + E3 * k := by
  dsimp only
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let v := curveSpeed F c t x
  let vx := deriv (curveSpeed F c t) x
  let k := m62Curvature F c t x
  let u := g.tangentNorm p (m63CurvatureJet F c 1 t x)
  let S := spatialUnitTangent F c t x
  let H := m62CurvatureVector F c t x
  let B := m63CurvatureJet F c 1 t x
  let de : TangentSpace (𝓡 n) p →L[ℝ] W := mfderiv (𝓡 n) 𝓘(ℝ, W) e p
  let E := coordinateHessian D e p
  let J := WithLp.toLp 2 (fun i : ι => D.covariantTensorDerivative
    (fun q w => D.hessian (fun z => e z i) q (w 0) (w 1)) p ![S, S, H])
  let Q := rampHorizontalCovariantDerivative D (fun r => c x r)
    (fun r => m62CurvatureVector F c r x) t - m63CurvatureJet F c 2 t x
  let Hhat : ℝ → ℝ → W := fun r y =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r) (m62CurvatureVector F c r y)
  let C := 2 * k ^ 3 + (K0 + 4 * K2) * k + 4 * K1 + 2 * k * u
  have hv : 0 < v := speed_pos F c hc (Ioo_subset_Icc_self ht) x
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hH : g.tangentNorm p H = k := rfl
  have hfirst : ‖deriv (Hhat t) x‖ ≤ v * (E1 * u + E2 * k) := by
    have hd := (hasDerivAt_embeddedCurvature_spatial F c hc he ht x).deriv
    change deriv (Hhat t) x = v • (de B + E S H) at hd
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hv]
    apply mul_le_mul_of_nonneg_left _ hv.le
    calc
      ‖de B + E S H‖ ≤ ‖de B‖ + ‖E S H‖ := norm_add_le _ _
      _ ≤ E1 * u + E2 * k := by
        have hEB := hE S H
        change ‖E S H‖ ≤ E2 * g.tangentNorm p S * g.tangentNorm p H at hEB
        rw [hS, hH, mul_one] at hEB
        exact add_le_add (hde B) hEB
  refine ⟨hfirst, ?_⟩
  have hQ : ‖de Q‖ ≤ E1 * C :=
    (hde Q).trans (mul_le_mul_of_nonneg_left
      (curvatureVector_diffusionError_norm_le F c hc h0 h1 h2 hBounds ht x) hE1)
  have hEB : ‖E S B‖ ≤ E2 * u := by
    have hb := hE S B
    change ‖E S B‖ ≤ E2 * g.tangentNorm p S * u at hb
    simpa only [hS, mul_one] using hb
  have hJb : ‖J‖ ≤ E3 * k := by
    have hb := hJ S S H
    change ‖J‖ ≤ E3 * g.tangentNorm p S * g.tangentNorm p S * g.tangentNorm p H at hb
    simpa only [hS, hH, mul_one] using hb
  have hdrift : ‖(vx / v ^ 3) • deriv (Hhat t) x‖ ≤
      (|vx| / v ^ 2) * (E1 * u + E2 * k) := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hv]
    calc
      (|vx| / v ^ 3) * ‖deriv (Hhat t) x‖ ≤
          (|vx| / v ^ 3) * (v * (E1 * u + E2 * k)) :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
      _ = _ := by field_simp
  have htwo : ‖(2 : ℝ) • E S B‖ ≤ 2 * E2 * u := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hEB (by norm_num : (0 : ℝ) ≤ 2)
  have heq : deriv (fun r => Hhat r x) t - (v ^ 2)⁻¹ • iteratedDeriv 2 (Hhat t) x =
      de Q - (vx / v ^ 3) • deriv (Hhat t) x - (2 : ℝ) • E S B - J := by
    have hd := (hasDerivAt_embeddedCurvature_time F c hc he ht x).deriv
    change deriv (fun r => Hhat r x) t =
      (v ^ 2)⁻¹ • iteratedDeriv 2 (Hhat t) x + de Q -
        (vx / v ^ 3) • deriv (Hhat t) x - (2 : ℝ) • E S B - J at hd
    rw [hd]
    abel
  change ‖deriv (fun r => Hhat r x) t - (v ^ 2)⁻¹ • iteratedDeriv 2 (Hhat t) x‖ ≤
    E1 * C + (|vx| / v ^ 2) * (E1 * u + E2 * k) + 2 * E2 * u + E3 * k
  rw [heq]
  calc
    ‖de Q - (vx / v ^ 3) • deriv (Hhat t) x - (2 : ℝ) • E S B - J‖ ≤
        ‖de Q - (vx / v ^ 3) • deriv (Hhat t) x - (2 : ℝ) • E S B‖ + ‖J‖ :=
      norm_sub_le _ _
    _ ≤ (‖de Q - (vx / v ^ 3) • deriv (Hhat t) x‖ + ‖(2 : ℝ) • E S B‖) + ‖J‖ :=
      add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ ‖de Q‖ + ‖(vx / v ^ 3) • deriv (Hhat t) x‖ + ‖(2 : ℝ) • E S B‖ + ‖J‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) (le_refl _)) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hQ hdrift) htwo) hJb

end PoincareConjecture.M63
