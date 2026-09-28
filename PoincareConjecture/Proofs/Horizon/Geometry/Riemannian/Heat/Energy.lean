import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.NoncompactEnergy











set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

private lemma contMDiff_slice_of_time_germ
    {F : ℝ × M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) := by
  intro y
  exact (hF y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)

private lemma contMDiff_square_slice
    {F : ℝ × M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y) ^ 2) := by
  exact (contMDiff_slice_of_time_germ hF).pow 2



theorem weighted_heat_energy_identity
    (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, φ x * deriv (fun s => F (s, x) ^ 2) t ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient φ x)
        (D.gradient (fun y => F (t, y) ^ 2) x) ∂g.volumeMeasure) -
        2 * ∫ x, φ x * g.inner x
          (D.gradient (fun y => F (t, y)) x)
          (D.gradient (fun y => F (t, y)) x) ∂g.volumeMeasure := by
  let H : M → ℝ := fun x => F (t, x) ^ 2
  have hslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) :=
    contMDiff_slice_of_time_germ hF
  have hHs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ H := by
    exact hslice.pow 2
  have hq : Integrable (fun x => φ x *
      g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x)) g.volumeMeasure :=
    (hφ.continuous.mul (D.continuous_inner_gradient hslice hslice)).integrable_of_hasCompactSupport
      hφc.mul_right
  have hgreen := D.integral_mul_laplacian hφ hHs hφc
  have hlap : Integrable (fun x => φ x * D.laplacian H x) g.volumeMeasure :=
    D.integrable_mul_laplacian hφ hHs hφc
  have hgrad : Integrable (fun x => g.inner x (D.gradient φ x) (D.gradient H x))
      g.volumeMeasure := D.integrable_inner_gradient hφ hHs hφc
  have hsq : ∀ x, deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x =
      -2 * g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) := by
    intro x
    simpa [H] using D.heat_square_identity hF hheat x
  have hres : Integrable (fun x => φ x *
      (deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x)) g.volumeMeasure := by
    apply (hq.const_mul (-2)).congr
    filter_upwards [] with x
    rw [hsq]
    ring
  have hsplit : ∀ x, φ x * deriv (fun s => F (s, x) ^ 2) t =
      φ x * D.laplacian H x + φ x *
        (deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x) := by
    intro x
    ring
  have hgreen' : (∫ x, φ x * D.laplacian H x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient φ x)
        (D.gradient (fun y => F (t, y) ^ 2) x) ∂g.volumeMeasure) := by
    simpa [H] using hgreen
  have hres_eq : (∫ x, φ x *
      (deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x) ∂g.volumeMeasure) =
      -2 * ∫ x, φ x * g.inner x
        (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) ∂g.volumeMeasure := by
    calc
      _ = ∫ x, (-2) * (φ x * g.inner x
          (D.gradient (fun y => F (t, y)) x)
          (D.gradient (fun y => F (t, y)) x)) ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hsq]
        ring
      _ = _ := by simp only [integral_const_mul]
  calc
    _ = ∫ x, (φ x * D.laplacian H x) + φ x *
        (deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x) ∂g.volumeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = (∫ x, φ x * D.laplacian H x ∂g.volumeMeasure) +
        ∫ x, φ x * (deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x)
          ∂g.volumeMeasure := integral_add hlap hres
    _ = -(∫ x, g.inner x (D.gradient φ x)
        (D.gradient (fun y => F (t, y) ^ 2) x) ∂g.volumeMeasure) +
        ∫ x, φ x * (deriv (fun s => F (s, x) ^ 2) t - D.laplacian H x)
          ∂g.volumeMeasure := by rw [hgreen']
    _ = _ := by rw [hres_eq]; ring

private lemma inner_gradient_sq_sq (D : LeviCivitaData g)
    {η f : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    g.inner x (D.gradient (fun y => η y ^ 2) x)
      (D.gradient (fun y => f y ^ 2) x) =
      4 * η x * f x * g.inner x (D.gradient η x) (D.gradient f x) := by
  simp only [pow_two, D.gradient_mul ((hη x).mdifferentiableAt (by simp))
    ((hη x).mdifferentiableAt (by simp)),
    D.gradient_mul ((hf x).mdifferentiableAt (by simp))
      ((hf x).mdifferentiableAt (by simp)),
    map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring




theorem heat_energy_cutoff_estimate (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) :
    (∫ x, η x ^ 2 * deriv (fun s => F (s, x) ^ 2) t ∂g.volumeMeasure) +
        (∫ x, η x ^ 2 * g.inner x (D.gradient (fun y => F (t, y)) x)
          (D.gradient (fun y => F (t, y)) x) ∂g.volumeMeasure) ≤
      4 * ∫ x, F (t, x) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)
        ∂g.volumeMeasure := by
  let f : M → ℝ := fun x => F (t, x)
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_slice_of_time_germ hF
  have hηsq : HasCompactSupport (fun x => η x ^ 2) := by
    rw [show (fun x => η x ^ 2) = η * η by funext x; simp [pow_two]]
    exact hηc.mul_right (f := η)
  have hq : Integrable (fun x => η x ^ 2 *
      g.inner x (D.gradient f x) (D.gradient f x)) g.volumeMeasure :=
    ((hη.pow 2).continuous.mul (D.continuous_inner_gradient hf hf)).integrable_of_hasCompactSupport
      hηsq.mul_right
  have he : Integrable (fun x => f x ^ 2 *
      g.inner x (D.gradient η x) (D.gradient η x)) g.volumeMeasure :=
    ((hf.pow 2).continuous.mul (D.continuous_inner_gradient hη hη)).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_left
  have hc := D.integrable_inner_gradient (hη.pow 2) (hf.pow 2) hηsq
  have hpoint (x : M) :
      -g.inner x (D.gradient (fun y => η y ^ 2) x)
        (D.gradient (fun y => f y ^ 2) x) ≤
      η x ^ 2 * g.inner x (D.gradient f x) (D.gradient f x) +
        4 * (f x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)) := by
    let v := η x • D.gradient f x + (2 * f x) • D.gradient η x
    have hv : 0 ≤ g.inner x v v := by
      by_cases h : v = 0
      · simp [h]
      · exact (g.pos x v h).le
    dsimp only [v] at hv
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
    rw [g.symm x (D.gradient f x) (D.gradient η x)] at hv
    rw [D.inner_gradient_sq_sq hη hf x]
    nlinarith
  have hi := integral_mono hc.neg (hq.add (he.const_mul 4)) hpoint
  simp only [Pi.neg_apply, Pi.add_apply] at hi
  rw [integral_neg, integral_add hq (he.const_mul 4), integral_const_mul] at hi
  have hid := D.weighted_heat_energy_identity hF hheat (hη.pow 2) hηsq
  change (∫ x, η x ^ 2 * deriv (fun s => F (s, x) ^ 2) t ∂g.volumeMeasure) +
      (∫ x, η x ^ 2 * g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) ≤
      4 * ∫ x, f x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure
  rw [hid]
  dsimp only [f] at hi ⊢
  linarith




theorem global_heat_energy_of_smooth_cutoff_bounds
    {q : M → ℝ} (hq : 0 ≤ᵐ[g.volumeMeasure] q)
    (hqmeas : AEMeasurable q g.volumeMeasure)
    {η : ℕ → M → ℝ}
    (hηsmooth : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (η j))
    (hηcompact : ∀ j, HasCompactSupport (η j))
    (hηnonneg : ∀ j x, 0 ≤ η j x)
    (hηlim : ∀ x, Tendsto (fun j ↦ η j x) atTop (𝓝 1))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j, Integrable (fun x ↦ η j x * q x) g.volumeMeasure ∧
      (∫ x, η j x * q x ∂g.volumeMeasure) ≤ C) :
    Integrable q g.volumeMeasure ∧
      (∫ x, q x ∂g.volumeMeasure) ≤ C := by
  have hηmeas : ∀ j, AEMeasurable (η j) g.volumeMeasure := by
    intro j
    exact (hηsmooth j).continuous.aemeasurable
  have hηlim' : ∀ᵐ x ∂g.volumeMeasure,
      Tendsto (fun j ↦ η j x) atTop (𝓝 1) :=
    Filter.Eventually.of_forall hηlim
  exact Poincare.Parabolic.integrable_of_cutoff_integral_bound
    hq hqmeas η hηmeas
    (fun j ↦ Filter.Eventually.of_forall (hηnonneg j)) hηlim' hC hbound



theorem global_heat_energy_of_exhaustion_cutoff_bounds
    {q : M → ℝ} (hq : 0 ≤ᵐ[g.volumeMeasure] q)
    (hqmeas : AEMeasurable q g.volumeMeasure) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j, Integrable (fun x ↦
      (Classical.choose (g.exists_smooth_compactSupport_cutoffs)) j x * q x)
        g.volumeMeasure ∧
      (∫ x, (Classical.choose (g.exists_smooth_compactSupport_cutoffs)) j x * q x
        ∂g.volumeMeasure) ≤ C) :
    Integrable q g.volumeMeasure ∧
      (∫ x, q x ∂g.volumeMeasure) ≤ C := by
  classical
  let hcut := g.exists_smooth_compactSupport_cutoffs
  let η := Classical.choose hcut
  have hspec := Classical.choose_spec hcut
  have hηsmooth : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (η j) := hspec.1
  have hηcompact : ∀ j, HasCompactSupport (η j) := hspec.2.1
  have hηrange : ∀ j x, η j x ∈ Set.Icc 0 1 := hspec.2.2.1
  have hηone : ∀ s : Set M, IsCompact s → ∀ᶠ j in atTop, EqOn (η j) 1 s :=
    hspec.2.2.2
  have hηlim : ∀ x, Tendsto (fun j ↦ η j x) atTop (𝓝 1) := by
    intro x
    have hev : ∀ᶠ j in atTop, η j x = 1 := by
      filter_upwards [hηone ({x} : Set M) isCompact_singleton] with j hj
      exact hj (by simp)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with j hj
    exact hj.symm
  apply global_heat_energy_of_smooth_cutoff_bounds hq hqmeas
    hηsmooth hηcompact (fun j x ↦ (hηrange j x).1) hηlim hC
  simpa only [η, hcut] using hbound


end PoincareConjecture.LeviCivitaData
