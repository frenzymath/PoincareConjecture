import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Maximum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.SpaceTime









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in

theorem liYau_cutoff_bound (D : LeviCivitaData g)
    (hn : 0 < n) {k A B : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ))
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t)
    {η : M → ℝ} (hηs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) (hη : ∀ x, η x ∈ Icc 0 1)
    (hgrad : ∀ x, g.inner x (D.gradient η x) (D.gradient η x) ≤ A * η x)
    (hlap : ∀ x, -B ≤ D.laplacian η x) :
    ∀ t, 0 < t → ∀ x,
      t * η x * (g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
          (D.gradient (fun y => Real.log (u (t, y))) x) -
        2 * deriv (fun s => Real.log (u (s, x))) t) ≤
      4 * (n : ℝ) * (1 + (B + ((n : ℝ) + 2) * A + k) * t) := by
  let f := fun p : ℝ × M => Real.log (u p)
  let w := fun t x => g.inner x (D.gradient (fun y => f (t, y)) x)
    (D.gradient (fun y => f (t, y)) x)
  let q := fun t x => 2 * (-D.laplacian (fun y => f (t, y)) x) + (1 - 2) * w t x
  have hf (t : ℝ) (ht : 0 < t) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x) :=
    contMDiffAt_log_of_pos
      (hu.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩))
      (hpos t ht x)
  have heq : ∀ t, 0 < t → ∀ x, q t x = w t x - 2 * deriv (fun s => f (s, x)) t :=
    (D.liYau_evolution_inequality hn hRic hu hpos hheat 2).1
  have hqs (t : ℝ) (ht : 0 < t) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2) (t, x) := by
    have hw := D.contMDiffAt_gradient_normSq_spacetime (hf t ht x)
    have hd := Poincare.Manifold.contMDiffAt_deriv_time (hf t ht x)
    apply (hw.sub (contMDiffAt_const.mul hd)).congr_of_eventuallyEq
    have htime : ∀ᶠ p : ℝ × M in 𝓝 (t, x), 0 < p.1 :=
      continuousAt_fst.eventually (eventually_gt_nhds ht)
    filter_upwards [htime] with p hp
    exact heq p.1 hp p.2
  have hcont : ContinuousOn (fun p : M × ℝ => η p.1 * q p.2 p.1) (univ ×ˢ Ioi 0) := by
    intro p hp
    have hswap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ Prod.swap p :=
      contMDiffAt_snd.prodMk contMDiffAt_fst
    have hh := (hqs p.2 hp.2 p.1).comp p hswap
    have hc : ContinuousAt (fun z : M × ℝ => q z.2 z.1) p := hh.continuousAt
    exact (((hηs.continuous.comp continuous_fst).continuousAt).mul hc).continuousWithinAt
  have hderiv (x : M) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => q s x) (deriv (fun s => q s x) t) t := by
    have hh := (hqs t ht x).comp t
      (contMDiffAt_id.prodMk (contMDiffAt_const (c := x)))
    exact (hh.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hbound := Poincare.Parabolic.weighted_quadratic_bound
    (q := fun x t => q t x) (qt := fun x t => deriv (fun s => q s x) t)
    (Nat.cast_pos.mpr hn) (show 0 ≤ B + ((n : ℝ) + 2) * A by positivity) hk
    hηc hη hcont hderiv (fun x t ht hposq hmax => ?_)
  · intro t ht x
    have h := hbound x t ht
    rw [heq t ht x] at h
    exact h
  · have hηpos : 0 < η x := lt_of_le_of_ne (hη x).1 (by
      intro he; rw [← he, zero_mul] at hposq; exact (lt_irrefl 0) hposq)
    have hqpos : 0 < q t x := (mul_pos_iff_of_pos_left hηpos).mp hposq
    apply D.liYau_cutoff_deriv_le_of_isLocalMax hn hηs
      (fun y => (hqs t ht y).comp y (contMDiffAt_const.prodMk contMDiffAt_id))
      (Filter.Eventually.of_forall hmax) hηpos (hη x).2 hqpos.le hA hk (hgrad x) (hlap x)
    · dsimp [q, w]
      ring
    · exact (D.liYau_evolution_inequality hn hRic hu hpos hheat 2).2 t ht x



theorem exists_liYau_bound_on_intrinsic_ball [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g) (hn : 0 < n) (hcomplete : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ × M → ℝ,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ) →
      (∀ t, 0 < t → ∀ x, 0 < u (t, x)) →
      (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
        (D.laplacian (fun y => u (t, y)) x) t) →
      ∀ t, 0 < t → ∀ x, (g.edist O x).toReal ≤ R →
        g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
          (D.gradient (fun y => Real.log (u (t, y))) x) -
          2 * deriv (fun s => Real.log (u (s, x))) t ≤ 4 * (n : ℝ) / t + C := by
  obtain ⟨η, B, hB, hηs, hηc, hη, hone, _, hgrad, hlap⟩ :=
    D.exists_intrinsic_ball_cutoff_laplacian_bound hcomplete O hR
  let A := 4 * (heatCutoffConstant / R) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := 4 * (n : ℝ) * (B + ((n : ℝ) + 2) * A + k)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u hu hpos hheat t ht x hx
  have h := D.liYau_cutoff_bound hn hk hA hB.le hRic hu hpos hheat hηs hηc hη
    hgrad (fun y => (abs_le.mp (hlap y)).1) t ht x
  rw [hone x hx, mul_one] at h
  apply (mul_le_mul_iff_right₀ ht).mp
  have he : t * (4 * (n : ℝ) / t + C) =
      4 * (n : ℝ) * (1 + (B + ((n : ℝ) + 2) * A + k) * t) := by
    dsimp [C]
    field_simp
  rw [he]
  exact h

end PoincareConjecture.LeviCivitaData
