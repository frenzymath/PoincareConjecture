import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture

private theorem cylinderClose_zeroth_normSquared_lt
    {ε : ℝ} {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose ε 0 B)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        B 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) < ε ^ 2 := by
  obtain ⟨_, bound, hbound, hjet⟩ := hB
  have hterm : roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        B 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) ≤
      roundCylinderJetErrorSquared 0 B ⌊ε⁻¹⌋₊ z := by
    dsimp only [roundCylinderJetErrorSquared]
    apply Finset.single_le_sum (f := fun k =>
      roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          B k (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)))
    · intro k _
      exact roundCylinderTensorNormSquared_nonneg z.1 _ _
    · simp
  exact hterm.trans_lt ((hjet z hz).trans_lt hbound)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem roundCylinderClose_scaled_pullback_quadratic_error
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    {ε Q : ℝ} (hε : 0 ≤ ε)
    (hclose : RoundCylinderClose ε 0 (fun z v w => Q * roundCylinderPullback g f z v w))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : RoundCylinderTangent z) :
    |Q * roundCylinderPullback g f z v v - EvolvingRoundCylinderMetric 0 z v v| ≤
      ε * EvolvingRoundCylinderMetric 0 z v v := by
  let : Bundle.RiemannianBundle (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
    ⟨roundCylinderProductMetric.toRiemannianMetric⟩
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  let x : RoundCylinderSpace := (c.symm p.1, p.2)
  let b := roundCylinderChartBasis z.1 p
  let : FiniteDimensional ℝ (RoundCylinderTangent x) := Module.Finite.of_basis b
  let D := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f x
  let A : RoundCylinderTangent x →ₗ[ℝ] RoundCylinderTangent x →ₗ[ℝ] ℝ :=
    Q • (g.inner (f x)).toBilinForm.comp D.toLinearMap D.toLinearMap -
      (roundCylinderProductMetric.inner x).toBilinForm
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) = roundCylinderGram 0 c p := by
    ext i j
    simp only [Matrix.of_apply, b, roundCylinderChartBasis_apply]
    exact roundCylinderChartFrame_gram z.1 p i j
  have hcoef (i j : Fin 3) : A (b i) (b j) =
      roundCylinderTensorCoefficient (fun z v w => Q * roundCylinderPullback g f z v w)
        c p i j - roundCylinderGram 0 c p i j := by
    change Q * roundCylinderPullback g f x (b i) (b j) -
      roundCylinderProductMetric.inner x (b i) (b j) = _
    rw [roundCylinderProductMetric_inner]
    simp only [b, roundCylinderChartBasis_apply]
    rfl
  have hA : (∑ i : Fin 2 → Fin 3, ∑ j : Fin 2 → Fin 3,
      (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
        A (b (i 0)) (b (i 1)) * A (b (j 0)) (b (j 1))) ≤ ε ^ 2 := by
    simp only [hGram, hcoef]
    exact (cylinderClose_zeroth_normSquared_lt hclose hz).le
  have hx : x = z := Prod.ext (c.left_inv (mem_chart_source _ z.1)) rfl
  have hbound : ∀ w : RoundCylinderTangent x,
      |Q * roundCylinderPullback g f x w w - EvolvingRoundCylinderMetric 0 x w w| ≤
        ε * EvolvingRoundCylinderMetric 0 x w w := by
    intro w
    have h := abs_bilinear_apply_self_le_of_inverse_gram_contraction_le A b hε hA w
    change |Q * roundCylinderPullback g f x w w - roundCylinderProductMetric.inner x w w| ≤
      ε * roundCylinderProductMetric.inner x w w at h
    simpa only [roundCylinderProductMetric_inner] using h
  exact Eq.mp (congrArg (fun y : RoundCylinderSpace =>
    ∀ w : RoundCylinderTangent y,
      |Q * roundCylinderPullback g f y w w - EvolvingRoundCylinderMetric 0 y w w| ≤
        ε * EvolvingRoundCylinderMetric 0 y w w) hx) hbound v

theorem edist_cylinderCover_slice_le
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    {ε Q : ℝ} (hε : 0 < ε) (hQ : 0 < Q)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0 (fun z v w => Q * roundCylinderPullback g f z v w))
    (q r : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (-ε⁻¹) ε⁻¹) :
    g.edist (f (q, a)) (f (r, a)) ≤
      ENNReal.ofReal (Real.sqrt ((1 + ε) * 2 / Q) * Real.pi) := by
  have hcoord (q : UnitTwoSphere) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f (q, a) :=
    hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ q, ha⟩)
  let F : UnitTwoSphere → M := fun q => f (q, a)
  have hF : ContMDiff (𝓡 2) (𝓡 3) 1 F := by
    intro q
    exact ((hcoord q).comp q (contMDiffAt_id.prodMk contMDiffAt_const)).of_le (by simp)
  have hderiv (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      mfderiv (𝓡 2) (𝓡 3) F q v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (q, a) (v, 0) := by
    dsimp only [TangentSpace] at v ⊢
    change mfderiv (𝓡 2) (𝓡 3) (f ∘ fun q : UnitTwoSphere => (q, a)) q v = _
    have h := mfderiv_comp_apply q ((hcoord q).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const) v
    simp only [id_eq, mfderiv_prod_left] at h
    exact h
  have hC : 0 < Real.sqrt ((1 + ε) * 2 / Q) := Real.sqrt_pos.mpr (by positivity)
  have hbound (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v)
        (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
        (Real.sqrt ((1 + ε) * 2 / Q)) ^ 2 * (roundSphereMetric 2).inner q v v := by
    have h := (abs_le.mp (roundCylinderClose_scaled_pullback_quadratic_error
      g f hε.le hclose (z := (q, a)) ha (v, 0))).2
    rw [hderiv, Real.sq_sqrt (by positivity : 0 ≤ (1 + ε) * 2 / Q)]
    simp only [roundCylinderPullback, EvolvingRoundCylinderMetric, sub_zero, mul_one,
      zero_mul, add_zero, roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hQ]
    simp only [roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner]
    nlinarith
  have hdist := (roundSphereMetric 2).edist_le_mul_of_inner_mfderiv_le g hF hC hbound q r
  have hpi : (roundSphereMetric 2).edist q r ≤ ENNReal.ofReal Real.pi := by
    rw [roundSphereMetric_edist_eq_angle (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (Real.arccos_le_pi _)
  exact hdist.trans (by
    rw [ENNReal.ofReal_mul hC.le]
    exact mul_le_mul' le_rfl hpi)

end PoincareConjecture
