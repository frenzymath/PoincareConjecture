import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorNorm

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem frame_inner_self_nonneg (x u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ g.inner x u u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (g.pos x _ hu).le

theorem connection_energy_le_of_directional_bound (D : LeviCivitaData g)
    (X : (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x)
    (x : EuclideanSpace ℝ (Fin n)) {a L : ℝ} (ha : 0 < a)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hdir : ∀ w : EuclideanSpace ℝ (Fin n),
      g.tangentNorm x (D.connection X x w) ≤ L * ‖w‖) :
    (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
      (D.connection X x (g.orthonormalBasis x i))) ≤ (n : ℝ) * L ^ 2 / a := by
  let e := g.orthonormalBasis x
  let eE : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      EuclideanSpace ℝ (Fin n) := fun i => e i
  have he (i) : g.inner x (e i) (e i) = 1 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change inner ℝ (e i) (e i) = 1
    rw [real_inner_self_eq_norm_sq, e.norm_eq_one]
    norm_num
  have hnorm (i) : ‖eE i‖ ^ 2 ≤ 1 / a := by
    apply (le_div_iff₀ ha).mpr
    have h := hlower (eE i)
    rw [he i] at h
    nlinarith
  have hterm (i) : g.inner x (D.connection X x (e i))
      (D.connection X x (e i)) ≤ L ^ 2 / a := by
    have hnn : 0 ≤ g.tangentNorm x (D.connection X x (e i)) := Real.sqrt_nonneg _
    have hsq := (sq_le_sq₀ hnn (hnn.trans (hdir (eE i)))).mpr (hdir (eE i))
    rw [RiemannianMetric.tangentNorm,
      Real.sq_sqrt (frame_inner_self_nonneg x _), mul_pow] at hsq
    calc
      _ ≤ L ^ 2 * ‖eE i‖ ^ 2 := hsq
      _ ≤ L ^ 2 * (1 / a) := mul_le_mul_of_nonneg_left (hnorm i) (sq_nonneg L)
      _ = _ := by ring
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), L ^ 2 / a :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring

theorem gradient_sub_reference_energy_le (D : LeviCivitaData g)
    {f q : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : DifferentiableAt ℝ f x) (hq : DifferentiableAt ℝ q x)
    (X : TangentSpace (𝓡 n) x) {a δ : ℝ} (ha : 0 < a)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hreference : g.tangentNorm x (D.gradient q x - X) ≤ δ) :
    g.inner x (D.gradient f x - X) (D.gradient f x - X) ≤
      (2 / a) * ‖fderiv ℝ (fun y => f y - q y) x‖ ^ 2 + 2 * δ ^ 2 := by
  have hgrad : D.gradient (fun y => f y - q y) x = D.gradient f x - D.gradient q x := by
    apply (g.inner_isInvertible x).injective
    ext v
    rw [D.inner_gradient, mvfderiv_fun_sub hf.mdifferentiableAt hq.mdifferentiableAt]
    simp only [map_sub, sub_apply, D.inner_gradient]
  have hsum : D.gradient f x - X =
      D.gradient (fun y => f y - q y) x + (D.gradient q x - X) := by
    rw [hgrad]
    abel
  have hdelta : g.inner x (D.gradient q x - X) (D.gradient q x - X) ≤ δ ^ 2 := by
    have hnn : 0 ≤ g.tangentNorm x (D.gradient q x - X) := Real.sqrt_nonneg _
    have h := (sq_le_sq₀ hnn (hnn.trans hreference)).mpr hreference
    simpa only [RiemannianMetric.tangentNorm,
      Real.sq_sqrt (frame_inner_self_nonneg x _)] using h
  have hadd (u v : EuclideanSpace ℝ (Fin n)) :
      g.inner x (u + v) (u + v) ≤ 2 * g.inner x u u + 2 * g.inner x v v := by
    have h := frame_inner_self_nonneg (g := g) x (u - v)
    simp only [map_sub, sub_apply] at h
    simp only [map_add, add_apply]
    rw [g.symm x v u] at h ⊢
    linarith
  rw [hsum]
  calc
    _ ≤ 2 * g.inner x (D.gradient (fun y => f y - q y) x)
        (D.gradient (fun y => f y - q y) x) +
        2 * g.inner x (D.gradient q x - X) (D.gradient q x - X) := hadd _ _
    _ ≤ 2 * (‖fderiv ℝ (fun y => f y - q y) x‖ ^ 2 / a) + 2 * δ ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (HarmonicCoordinates.gradient_energy_le_fderiv_sq D _ x ha hlower) (by norm_num))
        (mul_le_mul_of_nonneg_left hdelta (by norm_num))
    _ = _ := by ring

theorem integral_gradient_sub_reference_energy_le (D : LeviCivitaData g)
    {f q : EuclideanSpace ℝ (Fin n) → ℝ} {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q) (hX : ContDiff ℝ ∞ X)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    {a δ : ℝ} (ha : 0 < a)
    (hlower : ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hreference : ∀ x ∈ S, g.tangentNorm x
      ((show EuclideanSpace ℝ (Fin n) from D.gradient q x) - X x) ≤ δ) :
    (∫ x in S, g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)
      ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)) ≤
      (2 / a) * (∫ x in S, ‖fderiv ℝ (fun y => f y - q y) x‖ ^ 2) +
        2 * δ ^ 2 * (volume S).toReal := by
  have hfs := contMDiff_iff_contDiff.mpr hf
  have hV : ContDiff ℝ ∞ (fun x =>
      (show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x) :=
    (contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hfs)).sub hX
  have hVi : IntegrableOn
      (fun x => g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)
        ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)) S volume :=
    (contMDiff_vector_normSq (contMDiff_vectorSpace_iff_contDiff.mpr hV)).continuous.continuousOn.integrableOn_compact hS
  have hDi : IntegrableOn (fun x => ‖fderiv ℝ (fun y => f y - q y) x‖ ^ 2) S volume :=
    (((hf.sub hq).continuous_fderiv (by simp)).norm.pow 2).continuousOn.integrableOn_compact hS
  have hCi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => 2 * δ ^ 2) S volume :=
    continuousOn_const.integrableOn_compact hS
  calc
    _ ≤ ∫ x in S, (2 / a) * ‖fderiv ℝ (fun y => f y - q y) x‖ ^ 2 + 2 * δ ^ 2 := by
      apply integral_mono_ae hVi ((hDi.const_mul (2 / a)).add hCi)
      filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      exact D.gradient_sub_reference_energy_le
        (hf.differentiable (by simp) x) (hq.differentiable (by simp) x)
        (X x) ha (hlower x hx) (hreference x hx)
    _ = _ := by
      rw [integral_add (hDi.const_mul (2 / a)) hCi, integral_const_mul, integral_const]
      simp only [Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul]
      ring

end PoincareConjecture.LeviCivitaData
