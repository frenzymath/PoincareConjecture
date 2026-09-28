import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DomainEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Supports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

theorem liYau_cutoff_bound_of_lower_supports_on
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) {k A B : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : Set M} (hΩ : IsOpen Ω) {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ Ω))
    (hpos : ∀ t, 0 < t → ∀ x ∈ Ω, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x ∈ Ω, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t)
    {η : M → ℝ} (hηs : Continuous η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hη : ∀ x, η x ∈ Icc 0 1)
    (hsupport : ∀ x, 0 < η x → ∃ (U : Set M) (σ : M → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
      σ x = η x ∧ (∀ y ∈ U, σ y ≤ η y) ∧
      g.inner x (D.gradient σ x) (D.gradient σ x) ≤ A * η x ∧
      -B ≤ D.laplacian σ x) :
    ∀ t, 0 < t → ∀ x ∈ Ω,
      t * η x * (g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
          (D.gradient (fun y => Real.log (u (t, y))) x) -
        2 * deriv (fun s => Real.log (u (s, x))) t) ≤
      4 * (n : ℝ) * (1 + (B + ((n : ℝ) + 2) * A + k) * t) := by
  classical
  let f := fun p : ℝ × M => Real.log (u p)
  let w := fun t x => g.inner x (D.gradient (fun y => f (t, y)) x)
    (D.gradient (fun y => f (t, y)) x)
  let q := fun t x => 2 * (-D.laplacian (fun y => f (t, y)) x) + (1 - 2) * w t x
  let Q := fun t x => if x ∈ Ω then q t x else 0
  have hf (t : ℝ) (ht : 0 < t) (x : M) (hx : x ∈ Ω) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x) :=
    contMDiffAt_log_of_pos
      (hu.contMDiffAt ((isOpen_Ioi.prod hΩ).mem_nhds ⟨ht, hx⟩)) (hpos t ht x hx)
  have heq : ∀ t, 0 < t → ∀ x ∈ Ω,
      q t x = w t x - 2 * deriv (fun s => f (s, x)) t :=
    (D.liYau_evolution_inequality_on hn hRic hΩ hu hpos hheat 2).1
  have hqs (t : ℝ) (ht : 0 < t) (x : M) (hx : x ∈ Ω) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2) (t, x) := by
    have hw := D.contMDiffAt_gradient_normSq_spacetime (hf t ht x hx)
    have hd := Poincare.Manifold.contMDiffAt_deriv_time (hf t ht x hx)
    apply (hw.sub (contMDiffAt_const.mul hd)).congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioi.prod hΩ).mem_nhds ⟨ht, hx⟩] with p hp
    exact heq p.1 hp.1 p.2 hp.2
  have hspace (t : ℝ) (ht : 0 < t) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) Ω :=
    fun y hy => ((hqs t ht y hy).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).contMDiffWithinAt
  have hQgerm (t : ℝ) {x : M} (hx : x ∈ Ω) : Q t =ᶠ[𝓝 x] q t := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    simp only [Q, if_pos hy]
  have hcont : ContinuousOn (fun p : M × ℝ => η p.1 * Q p.2 p.1)
      (univ ×ˢ Ioi 0) := by
    intro p hp
    by_cases hx : p.1 ∈ Ω
    · have hswap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
          (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ Prod.swap p :=
        contMDiffAt_snd.prodMk contMDiffAt_fst
      have hh := (hqs p.2 hp.2 p.1 hx).comp p hswap
      have hc : ContinuousAt (fun z : M × ℝ => q z.2 z.1) p := hh.continuousAt
      apply ContinuousAt.continuousWithinAt
      apply (((hηs.comp continuous_fst).continuousAt).mul hc).congr_of_eventuallyEq
      filter_upwards [continuousAt_fst.eventually (hΩ.mem_nhds hx)] with z hz
      change z.1 ∈ Ω at hz
      simp only [Q, if_pos hz, Pi.mul_apply, Function.comp_apply]
    · have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hηΩ h))
      apply ContinuousAt.continuousWithinAt
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [continuousAt_fst.eventually hz] with z hz
      simp only [hz, Pi.zero_apply, zero_mul]
  have hderiv (x : M) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => Q s x) (deriv (fun s => Q s x) t) t := by
    by_cases hx : x ∈ Ω
    · have hh := (hqs t ht x hx).comp t
        (contMDiffAt_id.prodMk (contMDiffAt_const (c := x)))
      dsimp only [Q]
      simp only [if_pos hx]
      exact (hh.contDiffAt.differentiableAt (by simp)).hasDerivAt
    · simp only [Q, if_neg hx, deriv_const]
      exact hasDerivAt_const t 0
  have hbound := Poincare.Parabolic.weighted_quadratic_bound
    (q := fun x t => Q t x) (qt := fun x t => deriv (fun s => Q s x) t)
    (Nat.cast_pos.mpr hn) (show 0 ≤ B + ((n : ℝ) + 2) * A by positivity) hk
    hηc hη hcont hderiv (fun x t ht hposq hmax => ?_)
  · intro t ht x hx
    have h := hbound x t ht
    simpa only [Q, if_pos hx, heq t ht x hx] using h
  · have hηpos : 0 < η x := lt_of_le_of_ne (hη x).1 (by
      intro he; rw [← he, zero_mul] at hposq; exact (lt_irrefl 0) hposq)
    have hx : x ∈ Ω := hηΩ (subset_tsupport η (Function.mem_support.mpr hηpos.ne'))
    have hqpos : 0 < q t x := by
      simpa only [Q, if_pos hx] using (mul_pos_iff_of_pos_left hηpos).mp hposq
    obtain ⟨U, σ, hU, hxU, hσ, hση, hσle, hg, hl⟩ := hsupport x hηpos
    obtain ⟨χ, hχ, he⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hσ hxU
    obtain ⟨F, hF, hFq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hΩ (hspace t ht) hx
    have hχη : χ x = η x := he.self_of_nhds.trans hση
    have hFval : F x = q t x := hFq.self_of_nhds
    have hgrad : D.gradient χ x = D.gradient σ x := by
      unfold gradient
      rw [Poincare.mvfderiv_eq_of_eventuallyEq he]
    have hlocal : IsLocalMax (fun y => χ y * F y) x := by
      have hnear := (hspace t ht).continuousOn.continuousAt
        (hΩ.mem_nhds hx) |>.eventually (eventually_gt_nhds hqpos)
      filter_upwards [he, hFq, hQgerm t hx, hU.mem_nhds hxU, hnear] with y hey hFy hQy hy hqy
      rw [hey, hFy, hχη, hFval]
      exact (mul_le_mul_of_nonneg_right (hσle y hy) hqy.le).trans (by
        simpa only [hQy, Q, if_pos hx] using hmax y)
    have hevol := (D.liYau_evolution_inequality_on hn hRic hΩ hu hpos hheat 2).2 t ht x hx
    have hFderiv : mvfderiv (𝓡 n) F x = mvfderiv (𝓡 n) (q t) x :=
      Poincare.mvfderiv_eq_of_eventuallyEq hFq
    have hFlap := D.laplacian_eq_of_eventuallyEq hFq
    have hb := D.liYau_cutoff_deriv_le_of_isLocalMax hn hχ hF hlocal
      (hχη.symm ▸ hηpos) (hχη.symm ▸ (hη x).2) (hFval.symm ▸ hqpos.le) hA hk
      (by simpa only [hgrad, hχη] using hg)
      (by simpa only [D.laplacian_eq_of_eventuallyEq he] using hl)
      (show F x = -2 * D.laplacian (fun y => f (t, y)) x - w t x by
        rw [hFval]; dsimp [q]; ring)
      (qt := deriv (fun s => Q s x) t)
      (by simpa only [Q, if_pos hx, hFderiv, hFlap] using hevol)
    simpa only [hχη, hFval, Q, if_pos hx] using hb

end PoincareConjecture.LeviCivitaData
