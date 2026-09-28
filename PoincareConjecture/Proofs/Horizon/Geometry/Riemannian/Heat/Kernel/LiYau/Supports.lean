import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Maximum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.SpaceTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

theorem liYau_cutoff_bound_of_lower_supports
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) {k A B : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ))
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t)
    {η : M → ℝ} (hηs : Continuous η) (hηc : HasCompactSupport η)
    (hη : ∀ x, η x ∈ Icc 0 1)
    (hsupport : ∀ x, 0 < η x → ∃ (U : Set M) (σ : M → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
      σ x = η x ∧ (∀ y ∈ U, σ y ≤ η y) ∧
      g.inner x (D.gradient σ x) (D.gradient σ x) ≤ A * η x ∧
      -B ≤ D.laplacian σ x) :
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
  have hspace (t : ℝ) (ht : 0 < t) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) :=
    fun y => (hqs t ht y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hcont : ContinuousOn (fun p : M × ℝ => η p.1 * q p.2 p.1) (univ ×ˢ Ioi 0) := by
    intro p hp
    have hswap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ Prod.swap p :=
      contMDiffAt_snd.prodMk contMDiffAt_fst
    have hh := (hqs p.2 hp.2 p.1).comp p hswap
    have hc : ContinuousAt (fun z : M × ℝ => q z.2 z.1) p := hh.continuousAt
    exact (((hηs.comp continuous_fst).continuousAt).mul hc).continuousWithinAt
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
    obtain ⟨U, σ, hU, hxU, hσ, hση, hσle, hg, hl⟩ := hsupport x hηpos
    obtain ⟨χ, hχ, he⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hσ hxU
    have hχη : χ x = η x := he.self_of_nhds.trans hση
    have hgrad : D.gradient χ x = D.gradient σ x := by
      unfold gradient
      rw [Poincare.mvfderiv_eq_of_eventuallyEq he]
    have hlocal : IsLocalMax (fun y => χ y * q t y) x := by
      have hnear := (hspace t ht).continuous.continuousAt.eventually (eventually_gt_nhds hqpos)
      filter_upwards [he, hU.mem_nhds hxU, hnear] with y hey hy hqy
      rw [hey, hχη]
      exact (mul_le_mul_of_nonneg_right (hσle y hy) hqy.le).trans (hmax y)
    have hb := D.liYau_cutoff_deriv_le_of_isLocalMax hn hχ (hspace t ht) hlocal
      (hχη.symm ▸ hηpos) (hχη.symm ▸ (hη x).2) hqpos.le hA hk
      (by simpa only [hgrad, hχη] using hg)
      (by simpa only [D.laplacian_eq_of_eventuallyEq he] using hl)
      (show q t x = -2 * D.laplacian (fun y => f (t, y)) x - w t x by
        dsimp [q]; ring)
      ((D.liYau_evolution_inequality hn hRic hu hpos hheat 2).2 t ht x)
    simpa only [hχη] using hb

end PoincareConjecture.LeviCivitaData
