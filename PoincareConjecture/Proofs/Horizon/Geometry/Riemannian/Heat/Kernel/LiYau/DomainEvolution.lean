import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem exists_heat_slice_eq_near (D : LeviCivitaData g)
    {Ω : Set M} (hΩ : IsOpen Ω) {u : ℝ × M → ℝ} {t : ℝ}
    (hu : ∀ y ∈ Ω, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, y))
    (hpos : ∀ y ∈ Ω, 0 < u (t, y))
    (hheat : ∀ y ∈ Ω, HasDerivAt (fun s => u (s, y))
      (D.laplacian (fun z => u (t, z)) y) t) {x : M} (hx : x ∈ Ω) :
    ∃ v : ℝ × M → ℝ,
      (∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ v (t, y)) ∧
      (∀ y, 0 < v (t, y)) ∧
      (∀ y, HasDerivAt (fun s => v (s, y))
        (D.laplacian (fun z => v (t, z)) y) t) ∧
      ∀ᶠ y in 𝓝 x, ∀ s, v (s, y) = u (s, y) := by
  obtain ⟨χ, _, hχΩ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hΩ.mem_nhds hx)
  let U : ℝ × M → ℝ := fun p => χ p.2 * u p + (1 - χ p.2)
  have hU (y : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ U (t, y) := by
    by_cases hy : y ∈ Ω
    · have hχ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => χ p.2) (t, y) :=
        χ.contMDiffAt.comp (t, y) contMDiffAt_snd
      exact (hχ.mul (hu y hy)).add (contMDiffAt_const.sub hχ)
    · apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hχΩ h))
      filter_upwards [(continuous_snd.tendsto (t, y)).eventually hz] with p hp
      simp [U, hp]
  have hUpos (y : M) : 0 < U (t, y) := by
    by_cases hy : y ∈ Ω
    · by_cases hz : χ y = 0
      · simp [U, hz]
      have hmul := mul_pos (lt_of_le_of_ne χ.nonneg (Ne.symm hz)) (hpos y hy)
      have hle : χ y ≤ 1 := χ.le_one
      dsimp only [U]
      linarith
    · have hz : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hχΩ h))
      simp [U, hz]
  have hUt : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => U (t, y)) :=
    fun y => (hU y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  let r : M → ℝ := fun y => D.laplacian (fun z => U (t, z)) y -
    deriv (fun s => U (s, y)) t
  have hr : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ r :=
    (D.contMDiff_laplacian hUt).sub (fun y =>
      (Poincare.Manifold.contMDiffAt_deriv_time (hU y)).comp y
        (contMDiffAt_const.prodMk contMDiffAt_id))
  let v : ℝ × M → ℝ := fun p => U p + (p.1 - t) * r p.2
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro y
    exact (hU y).add ((contMDiffAt_fst.sub contMDiffAt_const).mul
      ((hr y).comp (t, y) contMDiffAt_snd))
  · intro y
    simpa only [v, sub_self, zero_mul, add_zero] using hUpos y
  · intro y
    have huTime := ((hU y).comp t (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
    have hdU := (huTime.differentiableAt (by simp)).hasDerivAt
    have hd := hdU.add (((hasDerivAt_id t).sub_const t).mul_const (r y))
    have he : deriv (fun s => U (s, y)) t + 1 * r y =
        D.laplacian (fun z => U (t, z)) y := by dsimp only [r]; ring
    convert hd.congr_deriv he using 1 <;> first | rfl | simp [v]
  · filter_upwards [χ.eventuallyEq_one.eventually_nhds, hΩ.mem_nhds hx] with y hy hyΩ
    have hχy : χ y = 1 := Filter.EventuallyEq.eq_of_nhds hy
    have hUy : (fun s => U (s, y)) = (fun s => u (s, y)) := by
      funext s
      simp [U, hχy]
    have hUs : (fun z => U (t, z)) =ᶠ[𝓝 y] (fun z => u (t, z)) := by
      filter_upwards [hy] with z hz
      simp [U, hz]
    have hr0 : r y = 0 := by
      dsimp only [r]
      rw [D.laplacian_eq_of_eventuallyEq hUs, hUy, (hheat y hyΩ).deriv, sub_self]
    intro s
    simp [v, hr0, congrFun hUy s]

omit [T2Space M] in
private theorem gradient_eq_of_eq_near (D : LeviCivitaData g)
    {f h : M → ℝ} {x : M} (he : f =ᶠ[𝓝 x] h) :
    D.gradient f x = D.gradient h x := by
  unfold gradient
  rw [Poincare.mvfderiv_eq_of_eventuallyEq he]

theorem liYau_evolution_inequality_on (D : LeviCivitaData g)
    (hn : 0 < n) {k : ℝ}
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : Set M} (hΩ : IsOpen Ω) {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ Ω))
    (hpos : ∀ t, 0 < t → ∀ x ∈ Ω, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x ∈ Ω, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t) (α : ℝ) :
    let f := fun s y => Real.log (u (s, y))
    let w := fun s y => g.inner y (D.gradient (f s) y) (D.gradient (f s) y)
    let q := fun s y => α * (-D.laplacian (f s) y) + (1 - α) * w s y
    (∀ t, 0 < t → ∀ x ∈ Ω, q t x = w t x - α * deriv (fun s => f s x) t) ∧
    (∀ t, 0 < t → ∀ x ∈ Ω,
      deriv (fun s => q s x) t - D.laplacian (q t) x ≤
        2 * mvfderiv (𝓡 n) (q t) x (D.gradient (f t) x) -
          (2 / (n : ℝ)) * D.laplacian (f t) x ^ 2 + 2 * k * w t x) := by
  let f := fun s y => Real.log (u (s, y))
  let w := fun s y => g.inner y (D.gradient (f s) y) (D.gradient (f s) y)
  let q := fun s y => α * (-D.laplacian (f s) y) + (1 - α) * w s y
  change (∀ t, 0 < t → ∀ x ∈ Ω, q t x = w t x - α * deriv (fun s => f s x) t) ∧
    (∀ t, 0 < t → ∀ x ∈ Ω,
      deriv (fun s => q s x) t - D.laplacian (q t) x ≤
        2 * mvfderiv (𝓡 n) (q t) x (D.gradient (f t) x) -
          (2 / (n : ℝ)) * D.laplacian (f t) x ^ 2 + 2 * k * w t x)
  have hpoint (t : ℝ) (ht : 0 < t) (x : M) (hx : x ∈ Ω) :
      q t x = w t x - α * deriv (fun s => f s x) t ∧
      deriv (fun s => q s x) t - D.laplacian (q t) x ≤
        2 * mvfderiv (𝓡 n) (q t) x (D.gradient (f t) x) -
          (2 / (n : ℝ)) * D.laplacian (f t) x ^ 2 + 2 * k * w t x := by
    obtain ⟨v, hv, hvpos, hvheat, hnear⟩ := D.exists_heat_slice_eq_near hΩ
      (fun y hy => hu.contMDiffAt ((isOpen_Ioi.prod hΩ).mem_nhds ⟨ht, hy⟩))
      (hpos t ht) (hheat t ht) hx
    let F := fun s y => Real.log (v (s, y))
    let W := fun s y => g.inner y (D.gradient (F s) y) (D.gradient (F s) y)
    let Q := fun s y => α * (-D.laplacian (F s) y) + (1 - α) * W s y
    have hF (s : ℝ) : F s =ᶠ[𝓝 x] f s :=
      hnear.mono fun y hy => congrArg Real.log (hy s)
    have hW : W t x = w t x := by
      dsimp only [W, w]
      rw [D.gradient_eq_of_eq_near (hF t)]
    have hQ : ∀ᶠ y in 𝓝 x, ∀ s, Q s y = q s y := by
      filter_upwards [hnear.eventually_nhds] with y hy s
      have he : F s =ᶠ[𝓝 y] f s := hy.mono fun z hz => congrArg Real.log (hz s)
      dsimp only [Q, q, W, w]
      rw [D.laplacian_eq_of_eventuallyEq he, D.gradient_eq_of_eq_near he]
    have hQt : Q t =ᶠ[𝓝 x] q t := hQ.mono fun y hy => hy t
    have hQtime : (fun s => Q s x) = (fun s => q s x) :=
      funext fun s => hQ.self_of_nhds s
    have hFtime : (fun s => F s x) = (fun s => f s x) :=
      funext fun s => congrArg Real.log (hnear.self_of_nhds s)
    have hlog := D.hasDerivAt_log_heat hv hvpos hvheat
    have hf : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p => Real.log (v p)) (t, y) :=
      fun y => contMDiffAt_log_of_pos (hv y) (hvpos y)
    constructor
    · have hid : Q t x = W t x - α * deriv (fun s => F s x) t := by
        rw [(hlog x).deriv]
        dsimp only [Q, W, F]
        ring
      rwa [hQt.eq_of_nhds, hW, hFtime] at hid
    · have hid := D.liYau_logarithmic_heat_evolution hf hlog α x
      change deriv (fun s => Q s x) t - D.laplacian (Q t) x =
        2 * mvfderiv (𝓡 n) (Q t) x (D.gradient (F t) x) -
          2 * (∑ i, ∑ j, D.hessian (F t) x
            (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2) -
          2 * D.ricci x (D.gradient (F t) x) (D.gradient (F t) x) at hid
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have htrace : D.laplacian (F t) x ^ 2 / (n : ℝ) ≤
          ∑ i, ∑ j, D.hessian (F t) x
            (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2 := by
        apply (div_le_iff₀ hn').mpr
        rw [mul_comm]
        exact D.laplacian_sq_le_dim_mul_hessian_normSq (F t) x
      have hr := hRic x (D.gradient (F t) x)
      have he : (2 / (n : ℝ)) * D.laplacian (F t) x ^ 2 =
          2 * (D.laplacian (F t) x ^ 2 / (n : ℝ)) := by ring
      have hle : deriv (fun s => Q s x) t - D.laplacian (Q t) x ≤
          2 * mvfderiv (𝓡 n) (Q t) x (D.gradient (F t) x) -
            (2 / (n : ℝ)) * D.laplacian (F t) x ^ 2 + 2 * k * W t x := by
        rw [hid, he]
        dsimp only [W]
        linarith
      rwa [hQtime, D.laplacian_eq_of_eventuallyEq hQt,
        Poincare.mvfderiv_eq_of_eventuallyEq hQt, D.gradient_eq_of_eq_near (hF t),
        D.laplacian_eq_of_eventuallyEq (hF t), hW] at hle
  exact ⟨fun t ht x hx => (hpoint t ht x hx).1, fun t ht x hx => (hpoint t ht x hx).2⟩

end PoincareConjecture.LeviCivitaData
