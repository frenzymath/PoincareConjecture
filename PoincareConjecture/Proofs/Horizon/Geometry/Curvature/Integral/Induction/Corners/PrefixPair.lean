import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.RestrictedPair
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Tightening
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.ObliqueProjection








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle InnerProductSpace BigOperators
namespace Poincare.CurvatureIntegral
private theorem prefix_pair_parameter_bounds (k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) :
    let a := 2 * ((k : ℝ) + 1) * δ
    0 ≤ a ∧ a ≤ 1 ∧ δ ≤ δ + 2 * a ∧
      δ + 2 * a ≤ 1 / (16 * ((k : ℝ) + 1)) := by
  dsimp only
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hK : 1 ≤ (k : ℝ) + 1 := by linarith
  have hmul := (le_div_iff₀ (by positivity : 0 < 256 * ((k : ℝ) + 1) ^ 2)).mp hsmall
  have ha : 0 ≤ 2 * ((k : ℝ) + 1) * δ := by positivity
  have hlinear : 256 * ((k : ℝ) + 1) * δ ≤ 1 := by
    have hx := mul_nonneg (show 0 ≤ (k : ℝ) * ((k : ℝ) + 1) by positivity) hδ
    nlinarith
  refine ⟨ha, by nlinarith, by linarith, ?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith
end Poincare.CurvatureIntegral



theorem PoincareConjecture.RiemannianMetric.strainer_prefix_openFiber_opposite_bounds
    {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (D : PoincareConjecture.LeviCivitaData g)
    (f h : Fin (k + 1) → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i w,
      D.hessian (f i) x w w ≤ C * g.inner x w w ∧
      D.hessian (h i) x w w ≤ C * g.inner x w w) :
    let a := 2 * ((k : ℝ) + 1) * δ
    let β := a / ((k : ℝ) + 1)
    let G := fun x => (1 - a) * h (Fin.last k) x + β * ∑ i : Fin k, h i.castSucc x
    let F := fun x (i : Fin k) => f i.castSucc x
    ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ G ∧
      ∃ hF : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ F,
        ∃ hreg : ∀ x ∈ U, Surjective
          (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) F x),
          ∀ v : Fin k → ℝ,
            letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
              ⟨finrank_euclideanSpace_fin⟩
            letI := openFiberChartedSpace (m := m) hF U hreg v
            letI := isManifold_openFiber (m := m) hF U hreg v
            let incl := openFiberIncl F U v
            let gL := g.openRegularFiberMetric hF U hreg v
            let φ := f (Fin.last k) ∘ incl
            let ψ := G ∘ incl
            ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) ∞ φ ∧
              ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) ∞ ψ ∧
              ∀ x : openFiber F U v,
                (1 / 2 ≤ gL.tangentNorm x (gL.gradient φ x) ∧
                  gL.tangentNorm x (gL.gradient φ x) ≤ 1) ∧
                (1 / 2 ≤ gL.tangentNorm x (gL.gradient ψ x) ∧
                  gL.tangentNorm x (gL.gradient ψ x) ≤ 1) ∧
                gL.inner x (gL.gradient φ x) (gL.gradient ψ x) ≤ -1 / 8 ∧
                ∀ w : TangentSpace (𝓡 m) x,
                  gL.leviCivitaData.hessian φ x w w ≤ 2 * C * gL.inner x w w ∧
                  gL.leviCivitaData.hessian ψ x w w ≤ 2 * C * gL.inner x w w := by
  classical
  dsimp only
  let a := 2 * ((k : ℝ) + 1) * δ
  let β := a / ((k : ℝ) + 1)
  let G := fun x => (1 - a) * h (Fin.last k) x + β * ∑ i : Fin k, h i.castSucc x
  let F := fun x (i : Fin k) => f i.castSucc x
  let e := δ + 2 * a
  have hnum := Poincare.CurvatureIntegral.prefix_pair_parameter_bounds k hδ hsmall
  have ha : 0 ≤ a := hnum.1
  have ha1 : a ≤ 1 := hnum.2.1
  have hδe : δ ≤ e := hnum.2.2.1
  have he16 : e ≤ 1 / (16 * ((k : ℝ) + 1)) := hnum.2.2.2
  have he : 0 ≤ e := hδ.trans hδe
  have he8 : e ≤ 1 / (8 * ((k : ℝ) + 1)) :=
    he16.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
  have he16' : e ≤ 1 / 16 := he16.trans
    (one_div_le_one_div_of_le (by norm_num) (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
  obtain ⟨hG, hGgrad, hGhess⟩ := D.strainer_tilt_differential_data
    (h (Fin.last k)) (fun i : Fin k => h i.castSucc) (hh _) (fun i => hh _) a
  simp only [Fintype.card_fin] at hG hGgrad hGhess
  simp only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient] at hGgrad
  change ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ G at hG
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hGunit (x : M) (hx : x ∈ U) :
      g.tangentNorm x (g.gradient G x) ≤ 1 ∧
      g.tangentNorm x (g.gradient G x - g.gradient (h (Fin.last k)) x) ≤ 2 * a := by
    change ‖g.gradient G x‖ ≤ 1 ∧ ‖g.gradient G x - g.gradient (h (Fin.last k)) x‖ ≤ 2 * a
    rw [hGgrad]
    simpa only [Fintype.card_fin] using
      Poincare.CurvatureIntegral.strainer_tilt_norm_bounds
        (g.gradient (h (Fin.last k)) x) (fun i : Fin k => g.gradient (h i.castSucc) x)
        ha ha1 (hunit x hx _).2 (fun i => (hunit x hx _).2)
  have hGcross (x : M) (hx : x ∈ U) (i : Fin k) :
      |g.inner x (g.gradient G x) (g.gradient (f i.castSucc) x)| ≤ e :=
    Poincare.CurvatureIntegral.abs_inner_le_of_strainer_perturbation
      (g.gradient (h (Fin.last k)) x) (g.gradient G x) (g.gradient (f i.castSucc) x)
      (hunit x hx _).1 (hGunit x hx).2
      (hcross x hx _ _ (Fin.castSucc_ne_last i).symm).2
  have hGtight (x : M) (hx : x ∈ U) (i : Fin k) :
      g.inner x (g.gradient G x) (g.gradient (f i.castSucc) x) ≤ 0 := by
    have hi := Poincare.CurvatureIntegral.inner_strainer_tilt_le
      (g.gradient (h (Fin.last k)) x) (fun i : Fin k => g.gradient (f i.castSucc) x)
      (fun i : Fin k => g.gradient (h i.castSucc) x) ha ha1
      (fun i => hopposite x hx i.castSucc)
      (fun i j hij => (le_abs_self _).trans
        (hcross x hx _ _ (fun he => hij (Fin.castSucc_inj.mp he))).2)
      (fun i => (le_abs_self _).trans (hcross x hx _ _ (Fin.castSucc_ne_last i).symm).2) i
    simp only [Fintype.card_fin] at hi
    change ⟪g.gradient G x, g.gradient (f i.castSucc) x⟫_ℝ ≤ 0
    rw [hGgrad]
    refine hi.trans ?_
    dsimp only [a]
    have hcoef : 2 * ((k : ℝ) + 1) * δ / ((k : ℝ) + 1) = 2 * δ := by field_simp
    rw [hcoef]
    linarith
  have hGpair (x : M) (hx : x ∈ U) :
      g.inner x (g.gradient (f (Fin.last k)) x) (g.gradient G x) ≤ -1 + 2 * e := by
    have hcs := abs_real_inner_le_norm (g.gradient (f (Fin.last k)) x)
      (g.gradient G x - g.gradient (h (Fin.last k)) x)
    have hbound := mul_le_mul (hunit x hx (Fin.last k)).1 (hGunit x hx).2
      (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have heq : ⟪g.gradient (f (Fin.last k)) x, g.gradient G x⟫_ℝ =
        ⟪g.gradient (f (Fin.last k)) x, g.gradient (h (Fin.last k)) x⟫_ℝ +
        ⟪g.gradient (f (Fin.last k)) x,
          g.gradient G x - g.gradient (h (Fin.last k)) x⟫_ℝ := by
      rw [inner_sub_right]; ring
    change ⟪g.gradient (f (Fin.last k)) x, g.gradient G x⟫_ℝ ≤ -1 + 2 * e
    rw [heq]
    have hop := hopposite x hx (Fin.last k)
    change ⟪g.gradient (f (Fin.last k)) x, g.gradient (h (Fin.last k)) x⟫_ℝ ≤
      -1 + 2 * δ at hop
    have habs := (le_abs_self _).trans (hcs.trans hbound)
    dsimp only [e]
    nlinarith
  have hGh (x : M) (hx : x ∈ U) (w : TangentSpace (𝓡 (m + k)) x) :
      D.hessian G x w w ≤ C * g.inner x w w := by
    rw [hGhess]
    have hq : 0 ≤ C * g.inner x w w := mul_nonneg hC (by
      change 0 ≤ ⟪w, w⟫_ℝ
      exact real_inner_self_nonneg)
    have hβ : 0 ≤ β := by dsimp only [β]; positivity
    have hsum : (∑ i : Fin k, D.hessian (h i.castSucc) x w w) ≤
        (k : ℝ) * (C * g.inner x w w) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin k) _ => (hH x hx i.castSucc w).2)
    have hcoef : β * ((k : ℝ) + 1) = a := by dsimp only [β]; field_simp
    have h1 := mul_le_mul_of_nonneg_left (hH x hx (Fin.last k) w).2 (sub_nonneg.mpr ha1)
    have h2 := mul_le_mul_of_nonneg_left hsum hβ
    change (1-a) * D.hessian (h (Fin.last k)) x w w +
      β * (∑ i : Fin k, D.hessian (h i.castSucc) x w w) ≤ C * g.inner x w w
    nlinarith [mul_nonneg hβ hq]
  have hFoldcross (x : M) (hx : x ∈ U) (i j : Fin k) (hij : i ≠ j) :
      |g.inner x (g.gradient (f i.castSucc) x) (g.gradient (f j.castSucc) x)| ≤ e :=
    (hcross x hx _ _ (fun he => hij (Fin.castSucc_inj.mp he))).1.trans hδe
  obtain ⟨hreg, hpairbounds⟩ := g.strainer_openFiber_gradient_pair_bounds
    (fun i : Fin k => f i.castSucc) (fun i => hf _) U
    (fun x (i : Fin k) => g.gradient (h i.castSucc) x) he he8
    (fun x hx i => (hunit x hx _).2)
    (fun x hx i => (hopposite x hx _).trans (by linarith)) hFoldcross
    (hf (Fin.last k)) hG (fun x hx => (hunit x hx _).1)
    (fun x hx => (hGunit x hx).1) hGpair
    (fun x hx i => (hcross x hx _ _ (Fin.castSucc_ne_last i).symm).1.trans hδe) hGcross
  let hF : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  refine ⟨hG, hF, hreg, ?_⟩
  intro v
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg v
  let := isManifold_openFiber (m := m) hF U hreg v
  let gL := g.openRegularFiberMetric hF U hreg v
  let incl := openFiberIncl F U v
  let φ := f (Fin.last k) ∘ incl
  let ψ := G ∘ incl
  have hincl := contMDiff_openFiberIncl (m := m) hF U hreg v
  refine ⟨(hf _).comp hincl, hG.comp hincl, ?_⟩
  intro x
  have hb := hpairbounds v x
  have hp : incl x ∈ U := x.1.2
  have hn := Poincare.CurvatureIntegral.strainer_parameter_bounds k he he8
  have hhess (χ : M → ℝ) (hχ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ χ)
      (hχcross : ∀ i : Fin k, -e ≤ g.inner (incl x) (g.gradient χ (incl x))
        (g.gradient (f i.castSucc) (incl x)) ∧
        g.inner (incl x) (g.gradient χ (incl x)) (g.gradient (f i.castSucc) (incl x)) ≤ 0)
      (hχhess : ∀ w, D.hessian χ (incl x) w w ≤ C * g.inner (incl x) w w) :
      ∀ w : TangentSpace (𝓡 m) x,
        gL.leviCivitaData.hessian (χ ∘ incl) x w w ≤ 2 * C * gL.inner x w w := by
    have hs := g.hessian_openRegularFiberMetric_le_of_tight_strainer hF U hreg v D hχ x
      (fun i => g.gradient (h i.castSucc) (incl x)) he hn.1 hn.2 he hC
      (fun i => (hunit _ hp _).2)
      (fun i => (hopposite _ hp _).trans (by linarith))
      (hFoldcross _ hp)
      (fun i j hij => htight _ hp _ _ (fun he => hij (Fin.castSucc_inj.mp he)))
      hχcross (fun i w => (hH _ hp _ w).1) hχhess
    intro w
    have hq : 0 ≤ gL.inner x w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (gL.pos x w hw).le
    exact (hs w).trans (mul_le_mul_of_nonneg_right
      (Poincare.CurvatureIntegral.strainer_hessian_coefficient_le_two_mul k he he8 hC) hq)
  have hφh := hhess (f (Fin.last k)) (hf _)
    (fun i => ⟨(abs_le.mp ((hcross _ hp _ _ (Fin.castSucc_ne_last i).symm).1.trans hδe)).1,
      htight _ hp _ _ (Fin.castSucc_ne_last i).symm⟩)
    (fun w => (hH _ hp _ w).1)
  have hψh := hhess G hG (fun i => ⟨(abs_le.mp (hGcross _ hp i)).1, hGtight _ hp i⟩)
    (hGh _ hp)
  refine ⟨hb.1, hb.2.1, ?_, fun w => ⟨hφh w, hψh w⟩⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : openFiber F U v → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  have hi (u z : TangentSpace (𝓡 m) x) : ⟪u, z⟫_ℝ = gL.inner x u z := rfl
  change gL.inner x (gL.gradient φ x) (gL.gradient ψ x) ≤ -1 / 8
  simpa only [hi, neg_div] using Poincare.InnerProductSpace.inner_le_neg_eighth_of_small_sum
    (gL.gradient φ x) (gL.gradient ψ x) hb.1.1 hb.2.1.1 hb.2.2 he16'
