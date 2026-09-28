import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Hitting
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.NormalizedField
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Transport
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.ObliqueProjection
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace Poincare.Manifold

theorem mfderiv_hittingMap_eq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {Φ : ℝ × M → M} {σ f : M → ℝ} {X : (z : M) → TangentSpace (𝓡 n) z}
    {y : M} {t : ℝ}
    (hΦ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) Φ (σ y, y))
    (hσ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) σ y)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (Φ (σ y, y)))
    (horbit : IsMIntegralCurveAt (I := 𝓡 n) (fun s => Φ (s, y)) X (σ y))
    (hlevel : (fun z => f (Φ (σ z, z))) =ᶠ[𝓝 y] (fun _ => t))
    (hcross : mvfderiv (𝓡 n) f (Φ (σ y, y)) (X (Φ (σ y, y))) ≠ 0)
    (v : TangentSpace (𝓡 n) y) :
    mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ z, z)) y v =
      mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ y, z)) y v -
        (mvfderiv (𝓡 n) f (Φ (σ y, y))
            (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ y, z)) y v) /
          mvfderiv (𝓡 n) f (Φ (σ y, y)) (X (Φ (σ y, y)))) • X (Φ (σ y, y)) := by
  let R : M → M := fun z => Φ (σ z, z)
  let L := mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ y, z)) y
  let ell := mvfderiv (𝓡 n) f (R y)
  let a := mvfderiv (𝓡 n) σ y v
  have hpair : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n))
      (fun z => (σ z, z)) y := hσ.prodMk mdifferentiableAt_id
  have hR : MDifferentiableAt (𝓡 n) (𝓡 n) R y := hΦ.comp (f := fun z => (σ z, z)) y hpair
  have hDR : mfderiv (𝓡 n) (𝓡 n) R y v = a • X (R y) + L v := by
    have hcomp := congrArg (fun A => A v)
      (mfderiv_comp (f := fun z => (σ z, z)) y hΦ hpair)
    erw [mfderiv_prodMk hσ mdifferentiableAt_id, mfderiv_id] at hcomp
    change mfderiv (𝓡 n) (𝓡 n) R y v =
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) Φ (σ y, y)
        (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) σ y v, v) at hcomp
    rw [mfderiv_prod_eq_add_apply hΦ, horbit.hasMFDerivAt.mfderiv] at hcomp
    change mfderiv (𝓡 n) (𝓡 n) R y v =
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) σ y v) • X (R y) + L v at hcomp
    simpa [a, mvfderiv, NormedSpace.fromTangentSpace] using hcomp
  have hnormal : ell (mfderiv (𝓡 n) (𝓡 n) R y v) = 0 := by
    have hcomp := congrArg (fun A => A v) (mfderiv_comp y hf hR)
    have hconst := hlevel.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ R) y = _ at hconst
    rw [hconst, mfderiv_const] at hcomp
    change 0 = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (R y) (mfderiv (𝓡 n) (𝓡 n) R y v) at hcomp
    simpa [ell, mvfderiv, NormedSpace.fromTangentSpace] using hcomp.symm
  rw [hDR, map_add, map_smul] at hnormal
  have ha : a = -(ell (L v) / ell (X (R y))) := by
    rw [← neg_div]
    apply (eq_div_iff hcross).mpr
    change a * ell (X (R y)) + ell (L v) = 0 at hnormal
    linarith
  change mfderiv (𝓡 n) (𝓡 n) R y v = L v - (ell (L v) / ell (X (R y))) • X (R y)
  rw [hDR, ha, neg_smul, sub_eq_add_neg, add_comm]

end Poincare.Manifold

theorem PoincareConjecture.LeviCivitaData.tangentNorm_mfderiv_hittingMap_le_of_expansion
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f h : M → ℝ} {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U) {l : ℝ} (hl : 0 < l)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient h y))
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {Φ : ℝ × M → M} {σ : M → ℝ}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo a b ×ˢ V))
    (hzero : ∀ y ∈ V, Φ (0,y) = y)
    (horbit : ∀ y ∈ V, (∀ s ∈ Ioo a b, Φ (s,y) ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) (fun s => Φ (s,y)) (D.normalizedGradient h) (Ioo a b))
    {y : M} (hy : y ∈ V) (hs : σ y ∈ Ioo a b)
    (hσ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) σ y)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (Φ (σ y,y)))
    {t : ℝ} (hlevel : (fun z => f (Φ (σ z,z))) =ᶠ[𝓝 y] (fun _ => t))
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hhunit : g.tangentNorm (Φ (σ y,y)) (D.gradient h (Φ (σ y,y))) ≤ 1)
    (hfunit : g.tangentNorm (Φ (σ y,y)) (D.gradient f (Φ (σ y,y))) ≤ 1)
    (hpair : g.inner (Φ (σ y,y)) (D.gradient f (Φ (σ y,y))) (D.gradient h (Φ (σ y,y))) ≤ -c)
    (hexp : ∀ w : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) h y w = 0 →
      g.tangentNorm (Φ (σ y,y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ y,z)) y w) ≤
        A * g.tangentNorm y w) (v : TangentSpace (𝓡 n) y) :
    g.tangentNorm (Φ (σ y,y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ z,z)) y v) ≤
      (1 + 1/c) * A * g.tangentNorm y v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi (z : M) (v w : TangentSpace (𝓡 n) z) : ⟪v,w⟫_ℝ = g.inner z v w := rfl
  let z := Φ (σ y,y)
  let L := mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (σ y,q)) y
  have hzy : z ∈ U := (horbit y hy).1 _ hs
  have hyU : y ∈ U := by
    simpa only [hzero y hy] using (horbit y hy).1 0 ⟨ha,hb⟩
  have hcrossne : mvfderiv (𝓡 n) f z (D.normalizedGradient h z) ≠ 0 :=
    (lt_of_le_of_lt (normalizedGradient_cross_le_of_pairing D f h z hl hc
      (hgrad z hzy) hhunit hpair) (by linarith)).ne
  have hΦd := (hΦ.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds
    (show (σ y,y) ∈ Ioo a b ×ˢ V from ⟨hs,hy⟩))).mdifferentiableAt (by simp)
  have hformula := Poincare.Manifold.mfderiv_hittingMap_eq
    hΦd hσ hf ((horbit y hy).2.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hs))
    hlevel hcrossne v
  have hqpos (q : M) (hq : q ∈ U) :
      0 < g.inner q (D.gradient h q) (D.gradient h q) := by
    rw [← hi, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (hl.trans_le (hgrad q hq))
  have hX := contMDiffOn_normalizedGradient_of_lower_bound D hU hh hl hgrad
  have htrans : L (D.normalizedGradient h y) = D.normalizedGradient h z :=
    Poincare.Manifold.mfderiv_localFlow_vectorField hU hV (hX.of_le (by simp))
      ha hb (hΦ.of_le (by simp)) hzero
      (fun q hq => (horbit q hq).1) (fun q hq => (horbit q hq).2) hy hs
  have hLu : L (D.gradient h y) =
      (g.inner y (D.gradient h y) (D.gradient h y) /
        g.inner z (D.gradient h z) (D.gradient h z)) • D.gradient h z := by
    have hrecover : D.gradient h y =
        g.inner y (D.gradient h y) (D.gradient h y) • D.normalizedGradient h y := by
      simp [normalizedGradient, smul_smul, (hqpos y hyU).ne']
    conv_lhs => rw [hrecover]
    rw [map_smul, htrans, normalizedGradient, smul_smul, div_eq_mul_inv]
  have hL : ∀ w : TangentSpace (𝓡 n) y, ⟪D.gradient h y,w⟫_ℝ=0 → ‖L w‖≤A*‖w‖ := by
    intro w hw
    apply hexp
    rw [← D.inner_gradient, ← hi]
    exact hw
  have hproject := Poincare.InnerProductSpace.norm_project_after_linearMap_le_of_angle
    L (D.gradient h y) (D.gradient h z) (D.gradient f z) hLu hc hpair hhunit hfunit hA hL v
  have hformula' : mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (σ q,q)) y v =
      L v - (g.inner z (D.gradient f z) (L v) /
        g.inner z (D.gradient f z) (D.gradient h z)) • D.gradient h z := by
    change mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (σ q,q)) y v =
      L v - (mvfderiv (𝓡 n) f z (L v) /
        mvfderiv (𝓡 n) f z (D.normalizedGradient h z)) • D.normalizedGradient h z at hformula
    rw [normalizedGradient, map_smul, smul_eq_mul, smul_smul,
      ← D.inner_gradient, ← D.inner_gradient] at hformula
    have hscale : (g.inner z (D.gradient f z) (L v) /
        ((g.inner z (D.gradient h z) (D.gradient h z))⁻¹ *
          g.inner z (D.gradient f z) (D.gradient h z))) *
        (g.inner z (D.gradient h z) (D.gradient h z))⁻¹ =
        g.inner z (D.gradient f z) (L v) / g.inner z (D.gradient f z) (D.gradient h z) := by
      have hp : g.inner z (D.gradient f z) (D.gradient h z) ≠ 0 :=
        (lt_of_le_of_lt hpair (by linarith)).ne
      field_simp [(hqpos z hzy).ne', hp]
    simpa only [hscale] using hformula
  rw [hformula']
  exact hproject

theorem PoincareConjecture.LeviCivitaData.exists_smooth_level_retraction_with_expansion
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f h : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U)
    {l H c : ℝ} (hl : 0 < l) (hH : 0 ≤ H) (hc : 0 < c)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient h y))
    (hhunit : ∀ y ∈ U, g.tangentNorm y (D.gradient h y) ≤ 1)
    (hfunit : ∀ y ∈ U, g.tangentNorm y (D.gradient f y) ≤ 1)
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) h y v = 0 → D.hessian h y v v ≤ H * g.inner y v v)
    (hpair : ∀ y ∈ U, g.inner y (D.gradient f y) (D.gradient h y) ≤ -c)
    {x : M} (hx : x ∈ U) :
    ∃ (V : Set M) (ε : ℝ) (R : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < ε ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ R
        (Ioo (f x - ε) (f x + ε) ×ˢ V) ∧
      (∀ t ∈ Ioo (f x - ε) (f x + ε), ∀ y ∈ V,
        R (t, y) ∈ U ∧ f (R (t, y)) = t ∧ (f y = t → R (t, y) = y)) ∧
      ∀ t ∈ Ioo (f x - ε) (f x + ε), ∀ y ∈ V, t ≤ f y →
        ∀ v : TangentSpace (𝓡 n) y,
          g.tangentNorm (R (t, y))
              (mfderiv (𝓡 n) (𝓡 n) (fun z => R (t, z)) y v) ≤
            (1 + 1 / c) * Real.exp ((H / l ^ 2) * ((f y - t) / c)) *
              g.tangentNorm y v := by

  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn (z : M) (v : TangentSpace (𝓡 n) z) : ‖v‖ = g.tangentNorm z v := rfl
  have hi (z : M) (v w : TangentSpace (𝓡 n) z) : ⟪v, w⟫_ℝ = g.inner z v w := rfl
  have hcross (y : M) (hy : y ∈ U) :
      mvfderiv (𝓡 n) f y (D.normalizedGradient h y) ≤ -c :=
    normalizedGradient_cross_le_of_pairing D f h y hl hc (hgrad y hy) (hhunit y hy) (hpair y hy)
  obtain ⟨V, ε, δ, Φ, σ, hVo, hxV, hVU, hε, hδ, hΦ, hzero, horbit, hσ, hR, hhit, hexp⟩ :=
    D.exists_smooth_normalizedGradient_hitting_map hU hf hh hl hH hc hgrad hhess hcross hx
  let R : ℝ × M → M := fun q => Φ (σ q, q.2)
  have hstays (t : ℝ) (ht : t ∈ Ioo (f x - ε) (f x + ε)) (y : M) (hy : y ∈ V) :
      R (t, y) ∈ U :=
    (horbit y hy).1 _ (hhit t ht y hy).1
  refine ⟨V, ε, R, hVo, hxV, hVU, hε, hR, ?_, ?_⟩
  · intro t ht y hy
    exact ⟨hstays t ht y hy, (hhit t ht y hy).2.1, (hhit t ht y hy).2.2.2.2⟩
  intro t ht y hy hty v
  let s := σ (t, y)
  let z := R (t, y)
  let L := mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (s, q)) y
  have hs : s ∈ Ioo (-δ) δ := (hhit t ht y hy).1
  have hs0 : 0 ≤ s := (hhit t ht y hy).2.2.2.1.mpr hty
  have hsy : s ∈ Ico 0 δ := ⟨hs0, hs.2⟩
  have hsle : s ≤ (f y - t) / c := by
    have hb : |s| ≤ |f y - t| / c := (hhit t ht y hy).2.2.1
    simpa only [abs_of_nonneg hs0, abs_of_nonneg (sub_nonneg.mpr hty)] using hb
  have hzy : z ∈ U := hstays t ht y hy
  have hσd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun q => σ (t, q)) y :=
    ((hσ.contMDiffAt ((isOpen_Ioo.prod hVo).mem_nhds ⟨ht, hy⟩)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hfd := (hf.contMDiffAt (hU.mem_nhds hzy)).mdifferentiableAt (by simp)
  have hhitloc : (fun q => f (R (t, q))) =ᶠ[𝓝 y] (fun _ => t) := by
    filter_upwards [hVo.mem_nhds hy] with q hq
    exact (hhit t ht q hq).2.1
  have hL : ∀ w : TangentSpace (𝓡 n) y, ⟪D.gradient h y, w⟫_ℝ = 0 →
      ‖L w‖ ≤ Real.exp ((H / l ^ 2) * s) * ‖w‖ := by
    intro w hw
    have hw' : mvfderiv (𝓡 n) h y w = 0 := by
      rw [← D.inner_gradient, ← hi]
      exact hw
    have hsq := (hexp y hy s hsy).2 w hw'
    change g.inner z (L w) (L w) ≤ g.inner y w w * Real.exp (2 * (H / l ^ 2) * s) at hsq
    rw [← hi, ← hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsq
    have he : (Real.exp ((H / l ^ 2) * s)) ^ 2 = Real.exp (2 * (H / l ^ 2) * s) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hnonneg : 0 ≤ Real.exp ((H / l ^ 2) * s) * ‖w‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    nlinarith [norm_nonneg (L w)]
  have hproject := D.tangentNorm_mfderiv_hittingMap_le_of_expansion
    hU hVo hh hl hgrad (by linarith : -δ < 0) hδ hΦ hzero horbit hy hs
    hσd hfd hhitloc hc (Real.exp_pos _).le (hhunit z hzy) (hfunit z hzy) (hpair z hzy)
    (fun w hw => hL w (by rw [hi, D.inner_gradient]; exact hw)) v
  apply hproject.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 + 1 / c)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle (div_nonneg hH (sq_nonneg l)))
