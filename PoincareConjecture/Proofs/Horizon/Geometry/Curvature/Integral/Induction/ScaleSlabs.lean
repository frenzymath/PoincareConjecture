import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Ascent








noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

private theorem slab_hessian_mul_radius_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (4 / (3 * (r / 2 - r / 64)) + (3 * r + r / 64) / 4 + 1) * r ≤ 5 := by
  have hsq : r ^ 2 ≤ 1 := by nlinarith
  have heq : (4 / (3 * (r / 2 - r / 64)) + (3 * r + r / 64) / 4 + 1) * r =
      256 / 93 + (193 : ℝ) / 256 * r ^ 2 + r := by
    field_simp
    ring
  rw [heq]
  nlinarith



theorem exists_proper_regular_slab_with_scale_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x, -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          (1 : ℝ) / 2 * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f) ∧
      (∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      ∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |f x - (g.edist p x).toReal| ≤ r / 65536 ∧
        (1 : ℝ) / 4 ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 2 ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ (5 / r) * g.inner x v v := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let H := 4 / (3 * (r / 2 - r / 64)) + (3 * r + r / 64) / 4 + 1
  have hHr : H * r ≤ 5 := slab_hessian_mul_radius_le hr hr1
  have herror : 2 * (r / 65536) / (r / 64) + H * (r / 64) / 2 < 1 / 4 := by
    have he : 2 * (r / 65536) / (r / 64) = (1 : ℝ) / 512 := by
      field_simp
      norm_num
    rw [he]
    nlinarith only [hHr]
  obtain ⟨f, hf, hproper, hreg, hband, hbound⟩ :=
    g.exists_proper_regular_slab_of_local_distance_ascent D hc (K := 1) zero_le_one hsec p
      (r₀ := r / 2) (r₁ := r) (R₀ := 2 * r) (R₁ := 3 * r)
      (T := r / 64) (ε := r / 65536) (η := 1) (c := (1 : ℝ) / 2)
      (a := 9 * r / 8) (b := 15 * r / 8)
      (by positivity) (by linarith) (by linarith) (by linarith) (by linarith)
      (by positivity) zero_lt_one (by norm_num) (by positivity) (by linarith)
      (by linarith) (by linarith)
      (by simpa only [one_mul] using herror.trans (by norm_num : (1 : ℝ) / 4 < 1 / 2))
      (fun y hy hy' => hascent y (by linarith) (by linarith))
  refine ⟨f, hf, hproper, hreg, hband, ?_⟩
  intro x hx hx'
  obtain ⟨hvalue, hlower, hupper, hhess⟩ := hbound x hx hx'
  simp only [one_mul] at hlower hhess
  refine ⟨hvalue, ?_, by simpa only [one_add_one_eq_two] using hupper, ?_⟩
  · apply le_trans _ hlower
    change (1 : ℝ) / 4 ≤ 1 / 2 - 2 * (r / 65536) / (r / 64) - H * (r / 64) / 2
    linarith only [herror]
  · intro v
    apply (hhess v).trans
    apply mul_le_mul_of_nonneg_right _ (by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg)
    change H ≤ 5 / r
    exact (le_div_iff₀ hr).mpr hHr

end PoincareConjecture.RiemannianMetric
