import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.RestrictedGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Hessian







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle BigOperators

namespace Poincare.CurvatureIntegral

theorem strainer_hessian_coefficient_le_two_mul (k : ℕ) {δ C : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) (hC : 0 ≤ C) :
    C + C * (k : ℝ) * δ / ((1 - 2 * δ) ^ 2 - (k : ℝ) * δ) ≤ 2 * C := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hmul := (le_div_iff₀ (by positivity : 0 < 8 * ((k : ℝ) + 1))).mp hsmall
  have hkδ : 0 ≤ (k : ℝ) * δ := mul_nonneg hk hδ
  have hδ8 : δ ≤ 1 / 8 := by nlinarith
  have hkδ8 : (k : ℝ) * δ ≤ 1 / 8 := by nlinarith
  have hden : 1 / 4 ≤ (1 - 2 * δ) ^ 2 - (k : ℝ) * δ := by
    nlinarith [sq_nonneg δ]
  have hdenpos : 0 < (1 - 2 * δ) ^ 2 - (k : ℝ) * δ := by linarith
  have hterm : C * (k : ℝ) * δ / ((1 - 2 * δ) ^ 2 - (k : ℝ) * δ) ≤ C := by
    apply (div_le_iff₀ hdenpos).mpr
    have h := mul_le_mul_of_nonneg_left
      (show (k : ℝ) * δ ≤ (1 - 2 * δ) ^ 2 - (k : ℝ) * δ by linarith) hC
    nlinarith only [h]
  linarith only [hterm]

end Poincare.CurvatureIntegral

theorem PoincareConjecture.RiemannianMetric.strainer_prefix_openFiber_bounds
    {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m+k) M) (D : PoincareConjecture.LeviCivitaData g)
    (f : Fin (k+1) → M → ℝ)
    (w : ∀ x : M, Fin (k+1) → TangentSpace (𝓡 (m+k)) x)
    (hf : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (f i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ)+1))) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1+2*δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ C * g.inner x v v) :
    let F := fun x (i : Fin k) => f i.castSucc x
    ∃ hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F,
      ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x),
        ∀ c : Fin k → ℝ,
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI := openFiberChartedSpace (m := m) hF U hreg c
          letI := isManifold_openFiber (m := m) hF U hreg c
          let gL := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hreg c g
          let φ := f (Fin.last k) ∘ openFiberIncl F U c
          ContMDiff (𝓡 m) 𝓘(ℝ,ℝ) ∞ φ ∧
            ∀ x : openFiber F U c,
              (1/2 ≤ gL.tangentNorm x (gL.gradient φ x) ∧
                gL.tangentNorm x (gL.gradient φ x) ≤ 1) ∧
              ∀ v : TangentSpace (𝓡 m) x,
                gL.leviCivitaData.hessian φ x v v ≤ (2*C) * gL.inner x v v := by
  let F := fun x (i : Fin k) => f i.castSucc x
  have hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  have hb := Poincare.CurvatureIntegral.strainer_parameter_bounds k hδ hsmall
  have hcrossOld (x : M) (hx : x ∈ U) (i j : Fin k) (hij : i ≠ j) :
      |g.inner x (g.gradient (f i.castSucc) x) (g.gradient (f j.castSucc) x)| ≤ δ :=
    hcross x hx _ _ (fun he => hij (Fin.castSucc_inj.mp he))
  let hreg := g.strainer_openFiber_regular (fun i : Fin k => f i.castSucc)
    (fun i => hf i.castSucc) U (fun x i => w x i.castSucc) hδ hb.1 hb.2
    (fun x hx i => (hunit x hx i.castSucc).2)
    (fun x hx i => hopposite x hx i.castSucc) hcrossOld
  refine ⟨hF,hreg,?_⟩
  intro c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let gL := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hreg c g
  let φ := f (Fin.last k) ∘ openFiberIncl F U c
  refine ⟨(hf (Fin.last k)).comp (contMDiff_openFiberIncl (m := m) hF U hreg c),?_⟩
  intro x
  let p := openFiberIncl F U c x
  have hp : p ∈ U := (x : U).2
  have hlower := PoincareConjecture.RiemannianMetric.tangentNorm_gradient_openRegularFiberMetric_ge_half
    hF U hreg c g (hf (Fin.last k)) x
    (fun i => w p i.castSucc) (w p (Fin.last k)) hδ hsmall
    (fun i => (hunit p hp i.castSucc).2)
    (fun i => hopposite p hp i.castSucc) (hcrossOld p hp)
    (hunit p hp (Fin.last k)).2 (hopposite p hp (Fin.last k))
    (fun i => hcross p hp _ _ (Fin.castSucc_ne_last i).symm)
  have hupper := PoincareConjecture.RiemannianMetric.tangentNorm_gradient_openRegularFiberMetric_le
    hF U hreg c g (hf (Fin.last k)) x
  refine ⟨⟨hlower,hupper.trans (hunit p hp (Fin.last k)).1⟩,?_⟩
  have hhess := PoincareConjecture.RiemannianMetric.hessian_openRegularFiberMetric_le_of_tight_strainer
    hF U hreg c D (hf (Fin.last k)) x (fun i => w p i.castSucc)
    hδ hb.1 hb.2 hδ hC
    (fun i => (hunit p hp i.castSucc).2)
    (fun i => hopposite p hp i.castSucc) (hcrossOld p hp)
    (fun i j hij => htight p hp _ _ (fun he => hij (Fin.castSucc_inj.mp he)))
    (fun i => ⟨(abs_le.mp (hcross p hp _ _ (Fin.castSucc_ne_last i).symm)).1,
      htight p hp _ _ (Fin.castSucc_ne_last i).symm⟩)
    (fun i v => hH p hp i.castSucc v) (fun v => hH p hp (Fin.last k) v)
  intro v
  have hv : 0 ≤ gL.inner x v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (gL.pos x v hz).le
  exact (hhess v).trans (mul_le_mul_of_nonneg_right
    (Poincare.CurvatureIntegral.strainer_hessian_coefficient_le_two_mul k hδ hsmall hC) hv)
