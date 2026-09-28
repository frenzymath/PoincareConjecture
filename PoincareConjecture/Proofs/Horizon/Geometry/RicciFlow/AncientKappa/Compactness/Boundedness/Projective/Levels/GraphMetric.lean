import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Projection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem roundCylinderClose_scaled_pullback_upper
    (g : RiemannianMetric 3 M) (Φ : RoundCylinderSpace → M)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 < r)
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : RoundCylinderTangent z) :
    roundCylinderPullback g Φ z v v ≤
      (1 + ε) * r ^ 2 * EvolvingRoundCylinderMetric 0 z v v := by
  have he := (abs_le.mp
    (roundCylinderClose_scaled_pullback_quadratic_error g Φ hε hclose hz v)).2
  have hb : r⁻¹ ^ 2 * roundCylinderPullback g Φ z v v ≤
      (1 + ε) * EvolvingRoundCylinderMetric 0 z v v := by linarith
  calc
    roundCylinderPullback g Φ z v v =
        r ^ 2 * (r⁻¹ ^ 2 * roundCylinderPullback g Φ z v v) := by field_simp
    _ ≤ r ^ 2 * ((1 + ε) * EvolvingRoundCylinderMetric 0 z v v) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg r)
    _ = (1 + ε) * r ^ 2 * EvolvingRoundCylinderMetric 0 z v v := by ring

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [IsManifold (𝓡 3) ∞ M] in

theorem hasDerivAt_cylinderCover_comp_axis
    (Φ : RoundCylinderSpace → M) {s : ℝ}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-s) s))
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (-s) s) :
    HasDerivAt (fun a : ℝ => f (Φ (q, a)))
      (mvfderiv (𝓡 3) f (Φ (q, t))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (q, t) (0, 1))) t := by
  have hmap := hΦ.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds (show (q, t) ∈ univ ×ˢ Ioo (-s) s from
      ⟨mem_univ _, ht⟩))
  have hpair := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) q t).prodMk
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t)
  have hcomp := ((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    ((hmap.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hpair)
  exact hcomp.hasFDerivAt.hasDerivAt

theorem cylinderCover_levelGraph_inner_mfderiv_le
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (Φ : RoundCylinderSpace → M)
    {ε r : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hr : 0 < r)
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w))
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {h : UnitTwoSphere → ℝ} (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-ε⁻¹) ε⁻¹)
    {c m G : ℝ} (hm : 0 < m) (hG : 0 ≤ G)
    (hlevel : ∀ q, f (Φ (q, h q)) = c)
    (hgrad : ∀ q, g.tangentNorm (Φ (q, h q)) (D.gradient f (Φ (q, h q))) ≤ G)
    (haxial : ∀ q, m * r ≤ |mvfderiv (𝓡 3) f (Φ (q, h q))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (q, h q) (0, 1))|)
    (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    let F := fun p : UnitTwoSphere => Φ (p, h p)
    g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v) (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
      (2 * r * (1 + 2 * G / m)) ^ 2 * (roundSphereMetric 2).inner q v v := by
  let F := fun p : UnitTwoSphere => Φ (p, h p)
  let x := F q
  let B := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (q, h q)
  let b := mvfderiv (𝓡 2) h q v
  let V := (roundSphereMetric 2).inner q v v
  let K := 2 * G / m
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV : 0 ≤ V := by
    by_cases hv : v = 0
    · simp [V, hv]
    · exact ((roundSphereMetric 2).pos q v hv).le
  have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV
  have hmap : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ (q, h q) :=
    hΦ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (q, h q) ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ from ⟨mem_univ _, hdom q⟩))
  have hFsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ F := by
    intro p
    exact (hΦ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (p, h p) ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ from ⟨mem_univ _, hdom p⟩))).comp p
        (contMDiffAt_id.prodMk (hh p))
  have hFderiv : mfderiv (𝓡 2) (𝓡 3) F q v = B (v, b) := by
    have hpair := (hasMFDerivAt_id (I := 𝓡 2) q).prodMk
      ((hh q).mdifferentiableAt (by simp)).hasMFDerivAt
    have heq := (hmap.mdifferentiableAt (by simp)).hasMFDerivAt.comp q hpair
    exact congrArg (fun A => A v) heq.mfderiv
  have hker : mvfderiv (𝓡 3) f x (B (v, b)) = 0 := by
    have hd := mvfderiv_comp_apply q ((hf (F q)).mdifferentiableAt (by simp))
      ((hFsmooth q).mdifferentiableAt (by simp)) v
    have heq : f ∘ F = fun _ => c := funext hlevel
    rw [heq, mvfderiv_const, zero_apply, hFderiv] at hd
    exact hd.symm
  have hhorizontal : g.inner x (B (v, 0)) (B (v, 0)) ≤
      (1 + ε) * r ^ 2 * (2 * V) := by
    have hb := roundCylinderClose_scaled_pullback_upper g Φ hε hr hclose
      (z := (q, h q)) (hdom q) (v, 0)
    simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
      roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
      sub_zero, mul_one, zero_mul, add_zero, V] using hb
  have hhorizontal' : g.inner x (B (v, 0)) (B (v, 0)) ≤ 4 * r ^ 2 * V := by
    apply hhorizontal.trans
    have hn := mul_nonneg (show 0 ≤ 1 - ε by linarith)
      (mul_nonneg (sq_nonneg r) hV)
    nlinarith only [hn]
  have hnorm : g.tangentNorm x (B (v, 0)) ≤ 2 * r * Real.sqrt V := by
    change Real.sqrt _ ≤ _
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) hr.le) (Real.sqrt_nonneg _), ?_⟩
    nlinarith only [hhorizontal', hsqrt]
  have hdfh : |mvfderiv (𝓡 3) f x (B (v, 0))| ≤ G * (2 * r * Real.sqrt V) :=
    (D.abs_mvfderiv_le_gradient_norm f x (B (v, 0))).trans
      (mul_le_mul (hgrad q) hnorm (Real.sqrt_nonneg _) hG)
  have hsplit : (v, b) = (v, 0) + b • (0, 1) := by
    change (v, b) = (v + b • (0 : TangentSpace (𝓡 2) q), 0 + b * 1)
    simp only [smul_zero, add_zero, mul_one, zero_add]
  rw [hsplit, map_add, map_smul, map_add, map_smul, smul_eq_mul] at hker
  have hbprod : |b| * |mvfderiv (𝓡 3) f x (B (0, 1))| =
      |mvfderiv (𝓡 3) f x (B (v, 0))| := by
    rw [← abs_mul, show b * mvfderiv (𝓡 3) f x (B (0, 1)) =
      -mvfderiv (𝓡 3) f x (B (v, 0)) by linarith only [hker], abs_neg]
  have hb : |b| ≤ K * Real.sqrt V := by
    apply (mul_le_mul_iff_left₀ (mul_pos hm hr)).mp
    calc
      |b| * (m * r) ≤ |b| * |mvfderiv (𝓡 3) f x (B (0, 1))| :=
        mul_le_mul_of_nonneg_left (haxial q) (abs_nonneg b)
      _ = |mvfderiv (𝓡 3) f x (B (v, 0))| := hbprod
      _ ≤ G * (2 * r * Real.sqrt V) := hdfh
      _ = K * Real.sqrt V * (m * r) := by dsimp [K]; field_simp
  have hbsq : b ^ 2 ≤ K ^ 2 * V := by
    have hb' := sq_le_sq₀ (abs_nonneg b) (mul_nonneg hK (Real.sqrt_nonneg V)) |>.mpr hb
    simpa only [sq_abs, mul_pow, hsqrt] using hb'
  have hmetric : g.inner x (B (v, b)) (B (v, b)) ≤
      (1 + ε) * r ^ 2 * (2 * V + b ^ 2) := by
    have hb := roundCylinderClose_scaled_pullback_upper g Φ hε hr hclose
      (z := (q, h q)) (hdom q) (v, b)
    simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
      roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
      sub_zero, mul_one, V, pow_two] using hb
  have hs : 0 ≤ r ^ 2 := sq_nonneg _
  have hmetric' : g.inner x (B (v, b)) (B (v, b)) ≤
      2 * r ^ 2 * (2 * V + K ^ 2 * V) := by
    apply hmetric.trans
    apply mul_le_mul
    · nlinarith [mul_nonneg (show 0 ≤ 1 - ε by linarith) hs]
    · exact add_le_add le_rfl hbsq
    · positivity
    · positivity
  change g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v) (mfderiv (𝓡 2) (𝓡 3) F q v) ≤ _
  rw [hFderiv]
  apply hmetric'.trans
  change 2 * r ^ 2 * (2 * V + K ^ 2 * V) ≤ (2 * r * (1 + K)) ^ 2 * V
  have hnonneg := mul_nonneg hs (mul_nonneg hV (show 0 ≤ 8 * K + 2 * K ^ 2 by positivity))
  nlinarith only [hnonneg]

theorem cylinderCover_levelGraph_tangentNorm_mfderiv_le
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (Φ : RoundCylinderSpace → M)
    {ε r : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hr : 0 < r)
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w))
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {h : UnitTwoSphere → ℝ} (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-ε⁻¹) ε⁻¹)
    {c m G : ℝ} (hm : 0 < m) (hG : 0 ≤ G)
    (hlevel : ∀ q, f (Φ (q, h q)) = c)
    (hgrad : ∀ q, g.tangentNorm (Φ (q, h q)) (D.gradient f (Φ (q, h q))) ≤ G)
    (haxial : ∀ q, m * r ≤ |mvfderiv (𝓡 3) f (Φ (q, h q))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (q, h q) (0, 1))|)
    (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    let F := fun p : UnitTwoSphere => Φ (p, h p)
    g.tangentNorm (F q) (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
      (2 * r * (1 + 2 * G / m)) * (roundSphereMetric 2).tangentNorm q v := by
  have hC : 0 ≤ 2 * r * (1 + 2 * G / m) :=
    mul_nonneg (mul_nonneg (by norm_num) hr.le) (by positivity)
  have hb := Real.sqrt_le_sqrt
    (cylinderCover_levelGraph_inner_mfderiv_le g D Φ hε hεone hr hΦ hclose
      hf hh hdom hm hG hlevel hgrad haxial q v)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC] at hb
  exact hb

end PoincareConjecture
