import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Ascent
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SlabNormalization

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

private theorem tight_scale_hessian_mul_radius_le {r δ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) :
    (4 / (3 * (r / 2 - δ * r / 1024)) +
      (3 * r + δ * r / 1024) / 4 + δ / 8) * r ≤ 5 := by
  have hT : δ * r / 1024 ≤ r / 64 := by
    nlinarith [mul_le_mul_of_nonneg_right hδquarter hr.le]
  have hden : 0 < 3 * (r / 2 - δ * r / 1024) := by linarith
  have hfirst : 4 / (3 * (r / 2 - δ * r / 1024)) * r ≤ 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hsq : r ^ 2 ≤ 1 := by nlinarith
  have hsecond : (3 * r + δ * r / 1024) / 4 * r ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hT hr.le]
  have hη : δ / 8 * r ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hδquarter hr.le]
  nlinarith only [hfirst, hsecond, hη]

private theorem tight_scale_losses {r δ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) :
    let T := δ * r / 1024
    let ε := δ ^ 2 * r / 1048576
    let H := 4 / (3 * (r / 2 - T)) + (3 * r + T) / 4 + δ / 8
    ε < r / 8 ∧ 2 * ε / T + H * T / 2 < 1 - δ / 8 ∧
      (1 - δ) * (1 + δ / 8) ≤ 1 - δ / 8 - 2 * ε / T - H * T / 2 := by
  let T := δ * r / 1024
  let ε := δ ^ 2 * r / 1048576
  let H := 4 / (3 * (r / 2 - T)) + (3 * r + T) / 4 + δ / 8
  have hH : H * r ≤ 5 := tight_scale_hessian_mul_radius_le hr hr1 hδ hδquarter
  have herror : 2 * ε / T = δ / 512 := by
    dsimp only [ε, T]
    field_simp
    ring
  have hHT : H * T / 2 ≤ 5 * δ / 2048 := by
    have h := mul_le_mul_of_nonneg_right hH hδ.le
    dsimp only [T]
    nlinarith only [h]
  have hloss : 2 * ε / T + H * T / 2 ≤ 9 * δ / 2048 := by
    rw [herror]
    linarith
  have hε : ε < r / 8 := by
    have hsq : δ ^ 2 ≤ 1 / 16 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq hr.le
    dsimp only [ε]
    nlinarith only [h, hr]
  exact ⟨hε, by change 2 * ε / T + H * T / 2 < _; linarith,
    by change (1 - δ) * (1 + δ / 8) ≤ 1 - δ / 8 - 2 * ε / T - H * T / 2
       nlinarith [sq_nonneg δ]⟩

theorem exists_proper_regular_slab_with_near_unit_gradient
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          (1 - δ / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    let τ := 1 / (1 + δ / 8)
    let ε := δ ^ 2 * r / 1048576
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      IsProperMap (I.restrictPreimage f) ∧
      (∀ x : M, f x ∈ I → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      ∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |f x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
        1 - δ ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 n) x,
          D.hessian f x v v ≤ (5 / r) * g.inner x v v := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let T := δ * r / 1024
  let ε := δ ^ 2 * r / 1048576
  let η := δ / 8
  let H := 4 / (3 * (r / 2 - T)) + (3 * r + T) / 4 + η
  let L := 1 - δ / 8 - 2 * ε / T - H * T / 2
  let τ := 1 / (1 + δ / 8)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hTsmall : T ≤ r / 64 := by
    dsimp only [T]
    nlinarith [mul_le_mul_of_nonneg_right hδquarter hr.le]
  have hTr : T < r / 2 := by linarith
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hH : H * r ≤ 5 := tight_scale_hessian_mul_radius_le hr hr1 hδ hδquarter
  have hHpos : 0 < H := by dsimp only [H]; positivity
  have hHle : H ≤ 5 / r := (le_div_iff₀ hr).mpr hH
  have hden : 0 < 1 + δ / 8 := by positivity
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτle : τ ≤ 1 := by
    dsimp only [τ]
    exact (div_le_one hden).mpr (by linarith)
  have hloss := tight_scale_losses hr hr1 hδ hδquarter
  change ε < r / 8 ∧ 2 * ε / T + H * T / 2 < 1 - δ / 8 ∧
    (1 - δ) * (1 + δ / 8) ≤ L at hloss
  have hlower : 1 - δ ≤ τ * L := by
    dsimp only [τ]
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hden).mpr hloss.2.2
  obtain ⟨f, hf, hproper, _, hband, hbounds⟩ :=
    g.exists_proper_regular_slab_of_local_distance_ascent D hc (K := 1)
      zero_le_one hsec p (r₀ := r / 2) (r₁ := r) (R₀ := 2 * r) (R₁ := 3 * r)
      (T := T) (ε := ε) (η := η) (c := 1 - δ / 8)
      (a := 9 * r / 8) (b := 15 * r / 8)
      hT hTr (by linarith) (by linarith) (by linarith) hε hη
      (by linarith) (by positivity) (by linarith) (by linarith [hloss.1])
      (by linarith [hloss.1]) (by simpa only [one_mul] using hloss.2.1)
      (fun y hy hy' => hascent y (by linarith) (by linarith))
  let F := fun x => τ * f x
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F := contMDiff_const.mul hf
  have hgrad (x : M) : D.gradient F x = τ • D.gradient f x := by
    apply (g.inner_isInvertible x).injective
    ext v
    rw [D.inner_gradient, mvfderiv_const_mul]
    simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
  have hnorm (x : M) :
      g.tangentNorm x (D.gradient F x) = τ * g.tangentNorm x (D.gradient f x) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [hgrad]
    change ‖τ • D.gradient f x‖ = τ * ‖D.gradient f x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  have hbandF (x : M) (hx : F x ∈ I) :
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r := by
    apply hband x
    simpa only [F, I, mem_Ioo, mul_lt_mul_iff_right₀ hτ] using hx
  have hboundsF (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |F x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
      1 - δ ≤ g.tangentNorm x (D.gradient F x) ∧
      g.tangentNorm x (D.gradient F x) ≤ 1 ∧
      ∀ v : TangentSpace (𝓡 n) x,
        D.hessian F x v v ≤ (5 / r) * g.inner x v v := by
    obtain ⟨hvalue, hlow, hupp, hhess⟩ := hbounds x hx hx'
    simp only [one_mul] at hlow hhess
    change L ≤ g.tangentNorm x (D.gradient f x) at hlow
    refine ⟨?_, ?_, ?_, ?_⟩
    · change |τ * f x - τ * (g.edist p x).toReal| ≤ τ * ε
      rw [← mul_sub, abs_mul, abs_of_pos hτ]
      exact mul_le_mul_of_nonneg_left hvalue hτ.le
    · rw [hnorm]
      exact hlower.trans (mul_le_mul_of_nonneg_left hlow hτ.le)
    · rw [hnorm]
      calc
        _ ≤ τ * (1 + η) := mul_le_mul_of_nonneg_left hupp hτ.le
        _ = 1 := by dsimp only [τ, η]; field_simp
    · intro v
      change D.hessian (fun y => τ * f y) x v v ≤ _
      rw [D.hessian_const_mul]
      have hv : 0 ≤ g.inner x v v := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        change 0 ≤ inner ℝ v v
        exact real_inner_self_nonneg
      calc
        _ ≤ τ * (H * g.inner x v v) := mul_le_mul_of_nonneg_left (hhess v) hτ.le
        _ = (τ * H) * g.inner x v v := by ring
        _ ≤ (5 / r) * g.inner x v v := mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right hτle hHpos.le).trans (by simpa using hHle)) hv
  have hproperF : IsProperMap (I.restrictPreimage F) := by
    let target : Ioo (9 * r / 8) (15 * r / 8) ≃ₜ I :=
      (Homeomorph.mulLeft₀ τ hτ.ne').subtype (fun x => by
        change x ∈ Ioo (9 * r / 8) (15 * r / 8) ↔
          τ * x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
        simp only [mem_Ioo, mul_lt_mul_iff_right₀ hτ])
    let source : (F ⁻¹' I) ≃ₜ (f ⁻¹' Ioo (9 * r / 8) (15 * r / 8)) :=
      (Homeomorph.refl M).subtype (fun x => by
        change τ * f x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) ↔
          f x ∈ Ioo (9 * r / 8) (15 * r / 8)
        simp only [mem_Ioo, mul_lt_mul_iff_right₀ hτ])
    exact (target.isProperMap.comp hproper).comp source.isProperMap
  refine ⟨F, hF, hproperF, ?_, hbandF, hboundsF⟩
  intro x hx
  apply (g.tangentNorm_gradient_pos_iff F x).mp
  exact (by linarith : 0 < 1 - δ).trans_le
    (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.1

end PoincareConjecture.RiemannianMetric
