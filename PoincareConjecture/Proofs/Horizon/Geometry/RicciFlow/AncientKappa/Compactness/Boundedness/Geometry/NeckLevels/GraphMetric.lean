import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Projection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem levelGraph_inner_mfderiv_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {h : UnitTwoSphere → ℝ} (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {c m G : ℝ} (hm : 0 < m) (hG : 0 ≤ G)
    (hlevel : ∀ q, f (N.coordinate_map (q, h q)) = c)
    (hgrad : ∀ q, g.tangentNorm (N.coordinate_map (q, h q))
      (D.gradient f (N.coordinate_map (q, h q))) ≤ G)
    (haxial : ∀ q, m * N.scale ≤
      |mvfderiv (𝓡 3) f (N.coordinate_map (q, h q))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (q, h q) (0, 1))|)
    (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    let F := fun p : UnitTwoSphere => N.coordinate_map (p, h p)
    g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v) (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
      (2 * N.scale * (1 + 2 * G / m)) ^ 2 * (roundSphereMetric 2).inner q v v := by
  let F := fun p : UnitTwoSphere => N.coordinate_map (p, h p)
  let x := F q
  let B := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, h q)
  let b := mvfderiv (𝓡 2) h q v
  let V := (roundSphereMetric 2).inner q v v
  let K := 2 * G / m
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV : 0 ≤ V := by
    by_cases hv : v = 0
    · simp [V, hv]
    · exact ((roundSphereMetric 2).pos q v hv).le
  have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV
  have hmap : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      N.coordinate_map (q, h q) := N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds
      (show (q, h q) ∈ N.cylinderDomain from ⟨mem_univ q, hdom q⟩))
  have hFsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ F := by
    intro p
    exact (N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds
        (show (p, h p) ∈ N.cylinderDomain from ⟨mem_univ p, hdom p⟩))).comp p
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
      (1 + N.epsilon) * N.scale ^ 2 * (2 * V) := by
    have hb := (N.pullback_metric_bounds (z := (q, h q)) (hdom q) (v, 0)).2
    simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
      roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
      sub_zero, mul_one, zero_mul, add_zero, V] using hb
  have hhorizontal' : g.inner x (B (v, 0)) (B (v, 0)) ≤ 4 * N.scale ^ 2 * V := by
    apply hhorizontal.trans
    have hn := mul_nonneg (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
      (mul_nonneg (sq_nonneg N.scale) hV)
    nlinarith only [hn]
  have hnorm : g.tangentNorm x (B (v, 0)) ≤ 2 * N.scale * Real.sqrt V := by
    change Real.sqrt _ ≤ _
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) (Real.sqrt_nonneg _), ?_⟩
    nlinarith only [hhorizontal', hsqrt]
  have hdfh : |mvfderiv (𝓡 3) f x (B (v, 0))| ≤
      G * (2 * N.scale * Real.sqrt V) :=
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
    apply (mul_le_mul_iff_left₀ (mul_pos hm N.scale_pos)).mp
    calc
      |b| * (m * N.scale) ≤ |b| * |mvfderiv (𝓡 3) f x (B (0, 1))| :=
        mul_le_mul_of_nonneg_left (haxial q) (abs_nonneg b)
      _ = |mvfderiv (𝓡 3) f x (B (v, 0))| := hbprod
      _ ≤ G * (2 * N.scale * Real.sqrt V) := hdfh
      _ = K * Real.sqrt V * (m * N.scale) := by dsimp [K]; field_simp
  have hbsq : b ^ 2 ≤ K ^ 2 * V := by
    have hb' := sq_le_sq₀ (abs_nonneg b) (mul_nonneg hK (Real.sqrt_nonneg V)) |>.mpr hb
    simpa only [sq_abs, mul_pow, hsqrt] using hb'
  have hmetric : g.inner x (B (v, b)) (B (v, b)) ≤
      (1 + N.epsilon) * N.scale ^ 2 * (2 * V + b ^ 2) := by
    have hb := (N.pullback_metric_bounds (z := (q, h q)) (hdom q) (v, b)).2
    simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
      roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
      sub_zero, mul_one, V, pow_two] using hb
  have hs : 0 ≤ N.scale ^ 2 := sq_nonneg _
  have hmetric' : g.inner x (B (v, b)) (B (v, b)) ≤
      2 * N.scale ^ 2 * (2 * V + K ^ 2 * V) := by
    apply hmetric.trans
    apply mul_le_mul
    · nlinarith [mul_nonneg (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half]) hs]
    · exact add_le_add le_rfl hbsq
    · positivity
    · positivity
  change g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v) (mfderiv (𝓡 2) (𝓡 3) F q v) ≤ _
  rw [hFderiv]
  apply hmetric'.trans
  change 2 * N.scale ^ 2 * (2 * V + K ^ 2 * V) ≤ (2 * N.scale * (1 + K)) ^ 2 * V
  have hnonneg := mul_nonneg hs (mul_nonneg hV (show 0 ≤ 8 * K + 2 * K ^ 2 by positivity))
  nlinarith only [hnonneg]



theorem levelGraph_tangentNorm_mfderiv_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {h : UnitTwoSphere → ℝ} (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {c m G : ℝ} (hm : 0 < m) (hG : 0 ≤ G)
    (hlevel : ∀ q, f (N.coordinate_map (q, h q)) = c)
    (hgrad : ∀ q, g.tangentNorm (N.coordinate_map (q, h q))
      (D.gradient f (N.coordinate_map (q, h q))) ≤ G)
    (haxial : ∀ q, m * N.scale ≤
      |mvfderiv (𝓡 3) f (N.coordinate_map (q, h q))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (q, h q) (0, 1))|)
    (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    let F := fun p : UnitTwoSphere => N.coordinate_map (p, h p)
    g.tangentNorm (F q) (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
      (2 * N.scale * (1 + 2 * G / m)) * (roundSphereMetric 2).tangentNorm q v := by
  have hC : 0 ≤ 2 * N.scale * (1 + 2 * G / m) :=
    mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) (by positivity)
  have hb := Real.sqrt_le_sqrt
    (N.levelGraph_inner_mfderiv_le D hf hh hdom hm hG hlevel hgrad haxial q v)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC] at hb
  exact hb

end PoincareConjecture.EpsilonNeck
