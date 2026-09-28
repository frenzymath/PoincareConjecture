import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Fiber
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Hessian.RegularFiber

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
  [IsManifold (𝓡 (m + k)) ∞ M]

local instance cornerHessian_ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem exists_hessian_restriction_gram_coefficients_openRegularFiberMetric
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
    (hreg : ∀ y ∈ U, Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f y))
    (c : Fin k → ℝ) {g : RiemannianMetric (m + k) M} (D : LeviCivitaData g)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (x : openFiber f U c) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let h := openRegularFiberMetric hf U hreg c g
    let p := openFiberIncl f U c x
    let dι := mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x
    ∃ a : Fin k → ℝ,
      (∀ i, g.inner p (g.gradient φ p) (g.gradient (fun y => f y i) p) =
        ∑ j, a j * g.inner p (g.gradient (fun y => f y j) p)
          (g.gradient (fun y => f y i) p)) ∧
      ∀ u v : TangentSpace (𝓡 m) x,
        h.leviCivitaData.hessian (φ ∘ openFiberIncl f U c) x u v =
          D.hessian φ p (dι u) (dι v) -
          ∑ i, a i * D.hessian (fun y => f y i) p (dι u) (dι v) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let h := openRegularFiberMetric hf U hreg c g
  let p := openFiberIncl f U c x
  let dι := mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x
  change ∃ a : Fin k → ℝ, _
  obtain ⟨a, ha, hH⟩ :=
    exists_hessian_restriction_coefficients_openRegularFiberMetric hf U hreg c D hφ x
  refine ⟨a, ?_, hH⟩
  intro i
  have hz (v : TangentSpace (𝓡 m) x) :
      g.inner p (g.gradient (fun y => f y i) p) (dι v) = 0 := by
    rw [g.inner_gradient]
    have hcomp := mvfderiv_comp x
      ((contMDiff_pi_space.mp hf i p).mdifferentiableAt (by simp))
      ((contMDiff_openFiberIncl (m := m) hf U hreg c x).mdifferentiableAt (by simp))
    have he : ((fun y => f y i) ∘ openFiberIncl f U c) = fun _ => c i := by
      funext z
      exact congrFun z.2 i
    rw [he, mvfderiv_const] at hcomp
    exact (congrArg (fun A => A v) hcomp).symm
  change g.inner p (g.gradient φ p) (g.gradient (fun y => f y i) p) = _
  rw [ha]
  simp only [map_add, add_apply, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  have hz' : g.inner p (dι (h.gradient (φ ∘ openFiberIncl f U c) x))
      (g.gradient (fun y => f y i) p) = 0 := by
    rw [g.symm]
    exact hz _
  rw [hz', zero_add]

theorem hessian_openRegularFiberMetric_le_of_tight_strainer
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
    (hreg : ∀ y ∈ U, Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f y))
    (c : Fin k → ℝ) {g : RiemannianMetric (m + k) M} (D : LeviCivitaData g)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (x : openFiber f U c)
    (w : Fin k → TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x))
    {δ ε β B : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hsmall : (k : ℝ) * δ < (1 - 2 * δ) ^ 2) (hε : 0 ≤ ε) (hβ : 0 ≤ β)
    (hw : ∀ i, g.tangentNorm (openFiberIncl f U c x) (w i) ≤ 1)
    (hopposite : ∀ i, g.inner (openFiberIncl f U c x)
      (g.gradient (fun y => f y i) (openFiberIncl f U c x)) (w i) ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j → |g.inner (openFiberIncl f U c x)
      (g.gradient (fun y => f y i) (openFiberIncl f U c x))
      (g.gradient (fun y => f y j) (openFiberIncl f U c x))| ≤ δ)
    (htight : ∀ i j, i ≠ j → g.inner (openFiberIncl f U c x)
      (g.gradient (fun y => f y i) (openFiberIncl f U c x))
      (g.gradient (fun y => f y j) (openFiberIncl f U c x)) ≤ 0)
    (hpair : ∀ i, -ε ≤ g.inner (openFiberIncl f U c x)
      (g.gradient φ (openFiberIncl f U c x))
      (g.gradient (fun y => f y i) (openFiberIncl f U c x)) ∧
      g.inner (openFiberIncl f U c x) (g.gradient φ (openFiberIncl f U c x))
        (g.gradient (fun y => f y i) (openFiberIncl f U c x)) ≤ 0)
    (hH : ∀ i v, D.hessian (fun y => f y i) (openFiberIncl f U c x) v v ≤
      β * g.inner (openFiberIncl f U c x) v v)
    (hHφ : ∀ v, D.hessian φ (openFiberIncl f U c x) v v ≤
      B * g.inner (openFiberIncl f U c x) v v) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let h := openRegularFiberMetric hf U hreg c g
    ∀ u : TangentSpace (𝓡 m) x,
      h.leviCivitaData.hessian (φ ∘ openFiberIncl f U c) x u u ≤
        (B + β * (k : ℝ) * ε / ((1 - 2 * δ) ^ 2 - (k : ℝ) * δ)) * h.inner x u u := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let h := openRegularFiberMetric hf U hreg c g
  let p := openFiberIncl f U c x
  let dι := mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, ha, hres⟩ :=
    exists_hessian_restriction_gram_coefficients_openRegularFiberMetric hf U hreg c D hφ x
  let A (i j : Fin k) := g.inner p (g.gradient (fun y => f y j) p)
    (g.gradient (fun y => f y i) p)
  have hdiag (i : Fin k) : (1 - 2 * δ) ^ 2 ≤ A i i := by
    have hn := Poincare.CurvatureIntegral.norm_lower_bound_of_opposite_pair
      (g.gradient (fun y => f y i) p) (w i) (hw i) (hopposite i)
    change (1 - 2 * δ) ^ 2 ≤ ⟪g.gradient (fun y => f y i) p,
      g.gradient (fun y => f y i) p⟫_ℝ
    rw [real_inner_self_eq_norm_sq]
    exact (sq_le_sq₀ (by linarith : 0 ≤ 1 - 2 * δ) (norm_nonneg _)).mpr hn
  have hAcross (i j : Fin k) (hij : i ≠ j) : |A i j| ≤ δ := hcross j i hij.symm
  have hAoff (i j : Fin k) (hij : i ≠ j) : A i j ≤ 0 := htight j i hij.symm
  have hpos : 0 < (1 - 2 * δ) ^ 2 - (Fintype.card (Fin k) : ℝ) * δ := by
    simpa only [Fintype.card_fin] using sub_pos.mpr hsmall
  have hAa (i : Fin k) : (∑ j, A i j * a j) =
      g.inner p (g.gradient φ p) (g.gradient (fun y => f y i) p) := by
    simpa only [A, mul_comm] using (ha i).symm
  have hnonpos := Poincare.CurvatureIntegral.coefficients_nonpos_of_diagonal_dominance
    A a hδ hdiag hAcross hAoff hpos (fun i => by rw [hAa]; exact (hpair i).2)
  have habs := Poincare.CurvatureIntegral.sum_abs_coefficients_le_of_diagonal_dominance
    A a hδ hε hdiag hAcross hAoff hpos (fun i => by
      rw [hAa, abs_of_nonpos (hpair i).2]
      linarith [(hpair i).1])
  have hsum : (∑ i, |a i|) ≤ (k : ℝ) * ε / ((1 - 2 * δ) ^ 2 - (k : ℝ) * δ) := by
    simpa only [Fintype.card_fin] using habs
  change ∀ u : TangentSpace (𝓡 m) x, _
  intro u
  have hq : 0 ≤ g.inner p (dι u) (dι u) := by
    change 0 ≤ ⟪(dι u : TangentSpace (𝓡 (m + k)) p), dι u⟫_ℝ
    exact real_inner_self_nonneg
  have hterm (i : Fin k) :
      -(a i * D.hessian (fun y => f y i) p (dι u) (dι u)) ≤
        |a i| * (β * g.inner p (dι u) (dι u)) := by
    rw [neg_mul_eq_neg_mul, ← abs_of_nonpos (hnonpos i)]
    exact mul_le_mul_of_nonneg_left (hH i (dι u)) (abs_nonneg _)
  rw [hres u u, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  calc
    _ ≤ B * g.inner p (dι u) (dι u) +
        ∑ i, |a i| * (β * g.inner p (dι u) (dι u)) :=
      add_le_add (hHφ (dι u)) (Finset.sum_le_sum fun i _ => hterm i)
    _ = (B + β * ∑ i, |a i|) * g.inner p (dι u) (dι u) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (B + β * ((k : ℝ) * ε / ((1 - 2 * δ) ^ 2 - (k : ℝ) * δ))) *
        g.inner p (dι u) (dι u) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hβ)) hq
    _ = _ := by
      rw [openRegularFiberMetric_inner]
      dsimp only [p, dι]
      ring

theorem tight_strainer_openFiber_hessian_le
    {g : RiemannianMetric (m + k) M} (D : LeviCivitaData g)
    (f : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i)) (U : Opens M)
    (w : ∀ y : M, Fin k → TangentSpace (𝓡 (m + k)) y)
    {δ ε β B : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hsmall : (k : ℝ) * δ < (1 - 2 * δ) ^ 2) (hε : 0 ≤ ε) (hβ : 0 ≤ β)
    (hw : ∀ y ∈ U, ∀ i, g.tangentNorm y (w y i) ≤ 1)
    (hopposite : ∀ y ∈ U, ∀ i, g.inner y (g.gradient (f i) y) (w y i) ≤ -1 + 2 * δ)
    (hcross : ∀ y ∈ U, ∀ i j, i ≠ j →
      |g.inner y (g.gradient (f i) y) (g.gradient (f j) y)| ≤ δ)
    (htight : ∀ y ∈ U, ∀ i j, i ≠ j →
      g.inner y (g.gradient (f i) y) (g.gradient (f j) y) ≤ 0)
    (c : Fin k → ℝ) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (hpair : ∀ y ∈ U, ∀ i,
      -ε ≤ g.inner y (g.gradient φ y) (g.gradient (f i) y) ∧
        g.inner y (g.gradient φ y) (g.gradient (f i) y) ≤ 0)
    (hH : ∀ y ∈ U, ∀ i v, D.hessian (f i) y v v ≤ β * g.inner y v v)
    (hHφ : ∀ y ∈ U, ∀ v, D.hessian φ y v v ≤ B * g.inner y v v) :
    let hreg := g.strainer_openFiber_regular f hf U w hδ hδhalf hsmall hw hopposite hcross
    letI := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U hreg c
    letI := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c
    let h := openRegularFiberMetric (contMDiff_pi_space.mpr hf) U hreg c g
    ∀ (x : openFiber (fun y i => f i y) U c) (u : TangentSpace (𝓡 m) x),
      h.leviCivitaData.hessian (φ ∘ openFiberIncl (fun y i => f i y) U c) x u u ≤
        (B + β * (k : ℝ) * ε / ((1 - 2 * δ) ^ 2 - (k : ℝ) * δ)) * h.inner x u u := by
  dsimp only
  intro x u
  exact hessian_openRegularFiberMetric_le_of_tight_strainer
    (contMDiff_pi_space.mpr hf) U _ c D hφ x
    (w (openFiberIncl (fun y i => f i y) U c x)) hδ hδhalf hsmall hε hβ
    (hw _ (x : U).2) (hopposite _ (x : U).2) (hcross _ (x : U).2)
    (htight _ (x : U).2) (hpair _ (x : U).2) (hH _ (x : U).2) (hHφ _ (x : U).2) u

end PoincareConjecture.RiemannianMetric
