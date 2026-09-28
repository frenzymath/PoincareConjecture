import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.LocalBound
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
lemma hasDerivAt_comp_affine_spacetimePath
    {f : ℝ × M → ℝ} {γ : ℝ → M} {a δ s : ℝ}
    (hf : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) f (a + δ * s, γ s))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ s) :
    HasDerivAt (fun r => f (a + δ * r, γ r))
      (δ * deriv (fun t => f (t, γ s)) (a + δ * s) +
        mvfderiv (𝓡 n) (fun x => f (a + δ * s, x)) (γ s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) s := by
  have ht : HasDerivAt (fun r : ℝ => a + δ * r) δ s := by
    simpa using ((hasDerivAt_id s).const_mul δ).const_add a
  have hpath := ht.hasFDerivAt.hasMFDerivAt.prodMk hγ.hasMFDerivAt
  have h := (hf.hasMFDerivAt.comp s hpath).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun r => f (a + δ * r, γ r))
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) f (a + δ * s, γ s)
      ((1 : ℝ) • δ, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) s at h
  rw [one_smul, mfderiv_prod_eq_add_apply hf] at h
  rw [mfderiv_eq_fderiv] at h
  change HasDerivAt (fun r => f (a + δ * r, γ r))
    ((fderiv ℝ (fun t => f (t, γ s)) (a + δ * s)) δ +
      mvfderiv (𝓡 n) (fun x => f (a + δ * s, x)) (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) s at h
  rw [fderiv_eq_smul_deriv, smul_eq_mul] at h
  exact h

lemma gradient_square_completion (D : LeviCivitaData g) (f : M → ℝ)
    (x : M) (v : TangentSpace (𝓡 n) x) {δ : ℝ} (hδ : 0 < δ) :
    -(g.inner x v v / (2 * δ)) ≤
      δ / 2 * g.inner x (D.gradient f x) (D.gradient f x) +
        mvfderiv (𝓡 n) f x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h : 0 ≤ g.inner x (δ • D.gradient f x + v) (δ • D.gradient f x + v) := by
    change 0 ≤ inner ℝ (δ • D.gradient f x + v) (δ • D.gradient f x + v)
    exact real_inner_self_nonneg
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h
  rw [g.symm x v (D.gradient f x)] at h
  simp only [D.inner_gradient] at h ⊢
  apply (neg_le_iff_add_nonneg).mpr
  apply (nonneg_of_mul_nonneg_left (b := 2 * δ) ?_ (by positivity))
  field_simp
  nlinarith

set_option backward.isDefEq.respectTransparency false in

lemma log_harnack_of_gradient_bound_on (D : LeviCivitaData g)
    {Ω : Set M} (hΩ : IsOpen Ω) {f : ℝ × M → ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (Ioi 0 ×ˢ Ω))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc 0 1))
    (hγΩ : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ Ω)
    {c B L : ℝ}
    (hbound : ∀ t, 0 < t → ∀ s ∈ Icc (0 : ℝ) 1,
      g.inner (γ s) (D.gradient (fun y => f (t, y)) (γ s))
        (D.gradient (fun y => f (t, y)) (γ s)) -
          2 * deriv (fun r => f (r, γ s)) t ≤ 2 * c / t + 2 * B)
    (hspeed : ∀ s ∈ Ioo (0 : ℝ) 1,
      g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ L ^ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    f (a, γ 0) ≤ f (b, γ 1) + c * Real.log (b / a) +
      B * (b - a) + L ^ 2 / (2 * (b - a)) := by
  let δ := b - a
  have hδ : 0 < δ := sub_pos.mpr hab
  let t := fun s : ℝ => a + δ * s
  have ht (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < t s :=
    add_pos_of_pos_of_nonneg ha (mul_nonneg hδ.le hs.1)
  let K := B * δ + L ^ 2 / (2 * δ)
  let F := fun s => f (t s, γ s) + c * Real.log (t s) + K * s
  have htcont : Continuous t := continuous_const.add (continuous_const.mul continuous_id)
  have hcont : ContinuousOn F (Icc 0 1) := by
    apply ((hf.continuousOn.comp (htcont.continuousOn.prodMk hγ.continuousOn)
      (fun s hs => ⟨ht s hs, hγΩ s hs⟩)).add
        ((Real.continuousOn_log.comp htcont.continuousOn
          (fun s hs => (ht s hs).ne')).const_mul c)).add
            (continuous_const.mul continuous_id).continuousOn
  have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F
        (δ * deriv (fun r => f (r, γ s)) (t s) +
          mvfderiv (𝓡 n) (fun y => f (t s, y)) (γ s)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) + c * (δ / t s) + K) s := by
    have hfs := (hf.contMDiffAt (x := (t s, γ s))
      ((isOpen_Ioi.prod hΩ).mem_nhds
        ⟨ht s (Ioo_subset_Icc_self hs), hγΩ s (Ioo_subset_Icc_self hs)⟩))
    have hγs := (hγ s (Ioo_subset_Icc_self hs)).contMDiffAt (Icc_mem_nhds hs.1 hs.2)
    have hd := hasDerivAt_comp_affine_spacetimePath
      (hfs.mdifferentiableAt (by simp)) (hγs.mdifferentiableAt one_ne_zero)
    have hdt : HasDerivAt t δ s := by
      simpa [t] using ((hasDerivAt_id s).const_mul δ).const_add a
    convert! (hd.add
      ((hdt.log (ht s (Ioo_subset_Icc_self hs)).ne').const_mul c)).add
        ((hasDerivAt_id s).const_mul K) using 1
    simp only [t, mul_one]
  have hmono : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1) hcont
    · intro s hs
      exact (hderiv s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hs
      have hq := hbound (t s) (ht s (Ioo_subset_Icc_self hs')) s (Ioo_subset_Icc_self hs')
      have hsq := D.gradient_square_completion (fun y => f (t s, y)) (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) hδ
      have hv := div_le_div_of_nonneg_right (hspeed s hs') (show 0 ≤ 2 * δ by positivity)
      have he : 2 * c / t s = 2 * (c / t s) := by ring
      rw [he] at hq
      have hscaled := mul_le_mul_of_nonneg_left hq (show 0 ≤ δ / 2 by positivity)
      dsimp only [K]
      rw [show c * (δ / t s) = δ * (c / t s) by ring]
      nlinarith
  have hend := hmono (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  have ht0 : t 0 = a := by simp [t]
  have ht1 : t 1 = b := by dsimp [t, δ]; ring
  dsimp only [F] at hend
  rw [ht0, ht1, mul_zero, mul_one] at hend
  rw [Real.log_div (ne_of_gt (ha.trans hab)) ha.ne']
  dsimp only [K, δ] at hend
  linarith

lemma log_harnack_of_gradient_bound (D : LeviCivitaData g)
    {f : ℝ × M → ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (Ioi 0 ×ˢ univ))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc 0 1))
    {c B L : ℝ}
    (hbound : ∀ t, 0 < t → ∀ s ∈ Icc (0 : ℝ) 1,
      g.inner (γ s) (D.gradient (fun y => f (t, y)) (γ s))
        (D.gradient (fun y => f (t, y)) (γ s)) -
          2 * deriv (fun r => f (r, γ s)) t ≤ 2 * c / t + 2 * B)
    (hspeed : ∀ s ∈ Ioo (0 : ℝ) 1,
      g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ L ^ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    f (a, γ 0) ≤ f (b, γ 1) + c * Real.log (b / a) +
      B * (b - a) + L ^ 2 / (2 * (b - a)) :=
  D.log_harnack_of_gradient_bound_on isOpen_univ hf hγ (fun _ _ => mem_univ _)
    hbound hspeed ha hab

end PoincareConjecture.LeviCivitaData
