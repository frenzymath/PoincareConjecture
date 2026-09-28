import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Level.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_bijective_lower_level_transport_of_hessian_ge_neg
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {U : Set M} (hU : IsOpen U) {l H a b : ℝ}
    (hl : 0 < l) (hH : 0 ≤ H) (hab : a ≤ b)
    (hgrad : ∀ x ∈ U, l ≤ g.tangentNorm x (D.gradient f x))
    (hhess : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      -H * g.inner x v v ≤ D.hessian f x v v)
    (hband : IsCompact {x | x ∈ U ∧ f x ∈ Icc a b}) :
    ∃ (V : Set M) (Q : M → M),
      IsOpen V ∧ {x | x ∈ U ∧ f x = b} ⊆ V ∧ V ⊆ U ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ Q V ∧
      MapsTo Q {x | x ∈ U ∧ f x = b} {x | x ∈ U ∧ f x = a} ∧
      SurjOn Q {x | x ∈ U ∧ f x = b} {x | x ∈ U ∧ f x = a} ∧
      InjOn Q {x | x ∈ U ∧ f x = b} ∧
      ∀ x ∈ U, f x = b → ∀ v : TangentSpace (𝓡 n) x,
        mvfderiv (𝓡 n) f x v = 0 →
        g.tangentNorm (Q x) (mfderiv (𝓡 n) (𝓡 n) Q x v) ≤
          Real.exp ((H / l ^ 2) * (b - a)) * g.tangentNorm x v := by
  have hgradneg (x : M) : D.gradient (fun y => -f y) x = -D.gradient f x := by
    simp only [gradient, mvfderiv_fun_neg, map_neg]
  have hnormneg (x : M) :
      g.tangentNorm x (D.gradient (fun y => -f y) x) =
        g.tangentNorm x (D.gradient f x) := by
    simp only [RiemannianMetric.tangentNorm, hgradneg, map_neg, neg_apply, neg_neg]
  have hhessneg (x : M) (v : TangentSpace (𝓡 n) x) :
      D.hessian (fun y => -f y) x v v = -D.hessian f x v v := by
    simpa only [neg_one_mul] using D.hessian_const_mul (-1) f x v v
  have hreg (x : M) (hx : x ∈ U) : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro hz
    have hg := (gradient_eq_zero_iff_mfderiv_eq_zero_manifold D f x).mpr hz
    have hh := hgrad x hx
    simp only [hg, RiemannianMetric.tangentNorm, map_zero, zero_apply,
      Real.sqrt_zero] at hh
    exact (not_le_of_gt hl) hh
  have hcompact (c : ℝ) (hc : c ∈ Icc a b) :
      IsCompact {x | x ∈ U ∧ f x = c} := by
    have h := hband.inter_right (isClosed_eq hf.continuous continuous_const
      (f := f) (g := fun _ => c))
    convert h using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun hx => ⟨⟨hx.1, hx.2 ▸ hc⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
  have hbandneg : IsCompact {x | x ∈ U ∧ -f x ∈ Icc (-b) (-a)} := by
    convert hband using 1
    ext x
    simp only [mem_ofPred_eq, mem_Icc, neg_le_neg_iff]
    tauto
  obtain ⟨V, δ, Φ, hV, hKV, hVU, hδ, hΦ, hzero, horbit, hbound⟩ :=
    D.exists_uniform_normalizedGradient_manifoldFlow_on_compact_band hU hf.neg.contMDiffOn
      hl hH (fun x hx => (hnormneg x).symm ▸ hgrad x hx)
      (fun x hx v _ => by rw [hhessneg]; linarith [hhess x hx v]) hbandneg
      (hcompact b ⟨hab, le_rfl⟩) (fun _ hx => hx.1) (sub_nonneg.mpr hab)
      (fun x hx => by rw [hx.2]) (fun x hx => by rw [hx.2]; linarith)
  let Q : M → M := fun x => Φ (b - a, x)
  have htime : b - a ∈ Ioo (-δ) (b - a + δ) := ⟨by linarith, by linarith⟩
  have hQs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Q V :=
    hΦ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x hx => ⟨htime, hx⟩)
  have hmaps : MapsTo Q {x | x ∈ U ∧ f x = b} {x | x ∈ U ∧ f x = a} := by
    intro x hx
    refine ⟨(horbit x (hKV hx)).1 (b - a) htime, ?_⟩
    have he := (hbound x (hKV hx) (b - a) ⟨sub_nonneg.mpr hab, le_rfl⟩).1
    change -f (Q x) = -f x + (b - a) at he
    rw [hx.2] at he
    linarith
  refine ⟨V, Q, hV, hKV, hVU, hQs, hmaps, ?_, ?_, ?_⟩
  · obtain ⟨W, ε, Ψ, hW, hKW, hWU, hε, hΨ, hzeroΨ, horbitΨ, hlevelΨ⟩ :=
      D.exists_normalizedGradient_flow_on_compact_regular_band hf hU hreg hband
        (hcompact a ⟨le_rfl, hab⟩) (fun _ hx => hx.1) (sub_nonneg.mpr hab)
        (fun _ hx => hx.2.ge) (fun x hx => by rw [hx.2]; linarith)
    intro y hy
    have hyW := hKW hy
    have htimeΨ : b - a ∈ Ioo (-ε) (b - a + ε) := ⟨by linarith, by linarith⟩
    have hx : Ψ (b - a, y) ∈ {x | x ∈ U ∧ f x = b} := by
      refine ⟨(horbitΨ y hyW).1 (b - a) htimeΨ, ?_⟩
      rw [hlevelΨ y hyW (b - a) ⟨sub_nonneg.mpr hab, le_rfl⟩, hy.2]
      ring
    refine ⟨Ψ (b - a, y), hx, ?_⟩
    have hX := (D.contMDiffOn_normalizedGradient_of_regular hU hf.contMDiffOn hreg).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have hneg : D.normalizedGradient (fun x => -f x) =
        fun x => -D.normalizedGradient f x :=
      funext (fun x => D.normalizedGradient_neg ((hf x).mdifferentiableAt (by simp)))
    have hreverse := Poincare.Manifold.reverse_integralCurve_endpoint hU hX
      (sub_nonneg.mpr hab) hε hδ (horbitΨ y hyW).1 (horbitΨ y hyW).2
      (by simpa only [hneg] using (horbit _ (hKV hx)).2)
      (hzero _ (hKV hx)).symm
    exact hreverse.trans (hzeroΨ y hyW)
  · intro x hx y hy hxy
    have hregneg (z : M) (hz : z ∈ U) :
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun w => -f w) z ≠ 0 := by
      change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (-f) z ≠ 0
      simpa only [mfderiv_neg, neg_ne_zero] using hreg z hz
    have hX := (D.contMDiffOn_normalizedGradient_of_regular hU
      hf.neg.contMDiffOn hregneg).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have heq := Poincare.Manifold.eqOn_of_isMIntegralCurveOn hU hX
      isOpen_Ioo isPreconnected_Ioo htime (horbit x (hKV hx)).1
      (horbit x (hKV hx)).2 (horbit y (hKV hy)).2 hxy
    have h0 : (0 : ℝ) ∈ Ioo (-δ) (b - a + δ) := ⟨by linarith, by linarith⟩
    exact (hzero x (hKV hx)).symm.trans ((heq h0).trans (hzero y (hKV hy)))
  · intro x hx hxb v hv
    have hquad := (hbound x (hKV ⟨hx, hxb⟩) (b - a)
      ⟨sub_nonneg.mpr hab, le_rfl⟩).2 v (by
        simpa only [mvfderiv_fun_neg, neg_apply, neg_eq_zero] using hv)
    change g.inner (Q x) (mfderiv (𝓡 n) (𝓡 n) Q x v)
      (mfderiv (𝓡 n) (𝓡 n) Q x v) ≤
        g.inner x v v * Real.exp (2 * (H / l ^ 2) * (b - a)) at hquad
    have hi (z : M) (w : TangentSpace (𝓡 n) z) : 0 ≤ g.inner z w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos z w hw).le
    have hsource := Real.sq_sqrt (hi x v)
    have htarget := Real.sq_sqrt (hi (Q x) (mfderiv (𝓡 n) (𝓡 n) Q x v))
    have hexp : (Real.exp ((H / l ^ 2) * (b - a))) ^ 2 =
        Real.exp (2 * (H / l ^ 2) * (b - a)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hn : 0 ≤ Real.exp ((H / l ^ 2) * (b - a)) * g.tangentNorm x v :=
      mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
    change Real.sqrt _ ≤ _
    dsimp only [RiemannianMetric.tangentNorm] at hn ⊢
    nlinarith [Real.sqrt_nonneg (g.inner (Q x) (mfderiv (𝓡 n) (𝓡 n) Q x v)
      (mfderiv (𝓡 n) (𝓡 n) Q x v))]

theorem exists_onto_lower_level_transport_of_hessian_ge_neg
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {U : Set M} (hU : IsOpen U) {l H a b : ℝ}
    (hl : 0 < l) (hH : 0 ≤ H) (hab : a ≤ b)
    (hgrad : ∀ x ∈ U, l ≤ g.tangentNorm x (D.gradient f x))
    (hhess : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      -H * g.inner x v v ≤ D.hessian f x v v)
    (hband : IsCompact {x | x ∈ U ∧ f x ∈ Icc a b}) :
    ∃ (V : Set M) (Q : M → M),
      IsOpen V ∧ {x | x ∈ U ∧ f x = b} ⊆ V ∧ V ⊆ U ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ Q V ∧
      MapsTo Q {x | x ∈ U ∧ f x = b} {x | x ∈ U ∧ f x = a} ∧
      SurjOn Q {x | x ∈ U ∧ f x = b} {x | x ∈ U ∧ f x = a} ∧
      ∀ x ∈ U, f x = b → ∀ v : TangentSpace (𝓡 n) x,
        mvfderiv (𝓡 n) f x v = 0 →
        g.tangentNorm (Q x) (mfderiv (𝓡 n) (𝓡 n) Q x v) ≤
          Real.exp ((H / l ^ 2) * (b - a)) * g.tangentNorm x v := by
  obtain ⟨V, Q, hV, htopV, hVU, hQ, hmaps, honto, _, hbound⟩ :=
    D.exists_bijective_lower_level_transport_of_hessian_ge_neg
      hf hU hl hH hab hgrad hhess hband
  exact ⟨V, Q, hV, htopV, hVU, hQ, hmaps, honto, hbound⟩

end PoincareConjecture.LeviCivitaData
