import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.Maximum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma exists_smooth_extension_near {Ω : Set M} (hΩ : IsOpen Ω)
    {f : M → ℝ} (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f Ω)
    {x : M} (hx : x ∈ Ω) :
    ∃ F : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] f := by
  obtain ⟨χ, -, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hΩ.mem_nhds hx)
  refine ⟨fun y => χ y * f y, ?_, ?_⟩
  · apply contMDiff_of_tsupport
    intro y hy
    have hyΩ : y ∈ Ω := hχ (tsupport_mul_subset_left hy)
    exact χ.contMDiffAt.mul (hf.contMDiffAt (hΩ.mem_nhds hyΩ))
  · filter_upwards [χ.eventuallyEq_one] with y hy
    simp [hy]

theorem laplacian_nonpos_of_isLocalMax_on
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    {f : M → ℝ} (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f Ω)
    {x : M} (hx : x ∈ Ω) (hmax : IsLocalMax f x) : D.laplacian f x ≤ 0 := by
  obtain ⟨F, hF, hEq⟩ := exists_smooth_extension_near hΩ hf hx
  have hmaxF : IsLocalMax F x := by
    filter_upwards [hmax, hEq] with y hy he
    simpa only [he, hEq.self_of_nhds] using hy
  rw [← D.laplacian_eq_of_eventuallyEq hEq]
  exact D.laplacian_nonpos_of_isLocalMax hF hmaxF

theorem laplacian_sub_on (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    {f h : M → ℝ} (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f Ω)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h Ω) {x : M} (hx : x ∈ Ω) :
    D.laplacian (fun y => f y - h y) x = D.laplacian f x - D.laplacian h x := by
  obtain ⟨F, hF, hFf⟩ := exists_smooth_extension_near hΩ hf hx
  obtain ⟨H, hH, hHh⟩ := exists_smooth_extension_near hΩ hh hx
  have he : (fun y => F y - H y) =ᶠ[𝓝 x] (fun y => f y - h y) := by
    filter_upwards [hFf, hHh] with y hy hy'
    rw [hy, hy']
  rw [← D.laplacian_eq_of_eventuallyEq he, D.laplacian_sub hF hH,
    D.laplacian_eq_of_eventuallyEq hFf, D.laplacian_eq_of_eventuallyEq hHh]

theorem nonpos_of_subsolution
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    (hc : IsCompact (closure Ω)) {F F' : M → ℝ → ℝ} {K a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (closure Ω ×ˢ Icc a b))
    (hsmooth : ∀ t ∈ Ioc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => F x t) Ω)
    (hderiv : ∀ x ∈ Ω, ∀ t ∈ Ioc a b,
      HasDerivWithinAt (F x) (F' x t) (Icc a b) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc a b,
      F' x t ≤ D.laplacian (fun y => F y t) x + K * F x t)
    (hboundary : ∀ x ∈ closure Ω, x ∉ Ω → ∀ t ∈ Icc a b, F x t ≤ 0)
    (hinit : ∀ x ∈ closure Ω, F x a ≤ 0) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b, F x t ≤ 0 := by
  let : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hc
  have hcont : ContinuousOn
      (fun p : closure Ω × ℝ => F p.1 p.2) (univ ×ˢ Icc a b) := by
    apply hF.comp
      (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn)
    exact fun p hp => ⟨p.1.property, hp.2⟩
  have hcompare := Poincare.Parabolic.Dirichlet.nonpos_of_deriv_le_mul_at_max
    (s := {x : closure Ω | (x : M) ∈ Ω})
    (F := fun (x : closure Ω) t => F x t) (F' := fun (x : closure Ω) t => F' x t)
    (K := K) hcont (fun x hx t ht => hderiv x hx t ht)
    (fun x hx t ht _ hmax => ?_)
    (fun x hx t ht => hboundary x x.property hx t ht)
    (fun x => hinit x x.property)
  · intro x hx t ht
    exact hcompare ⟨x, hx⟩ t ht
  · have hlocal : IsLocalMax (fun y => F y t) (x : M) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hmax ⟨y, subset_closure hy⟩
    have hlap := laplacian_nonpos_of_isLocalMax_on D hΩ (hsmooth t ht) hx hlocal
    exact (hsub x hx t ht).trans (by linarith)

theorem le_of_subsolution_supersolution
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    (hc : IsCompact (closure Ω)) {F G F' G' : M → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (closure Ω ×ˢ Icc a b))
    (hG : ContinuousOn (Function.uncurry G) (closure Ω ×ˢ Icc a b))
    (hFs : ∀ t ∈ Ioc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => F x t) Ω)
    (hGs : ∀ t ∈ Ioc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => G x t) Ω)
    (hFd : ∀ x ∈ Ω, ∀ t ∈ Ioc a b,
      HasDerivWithinAt (F x) (F' x t) (Icc a b) t)
    (hGd : ∀ x ∈ Ω, ∀ t ∈ Ioc a b,
      HasDerivWithinAt (G x) (G' x t) (Icc a b) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc a b, F' x t ≤ D.laplacian (fun y => F y t) x)
    (hsuper : ∀ x ∈ Ω, ∀ t ∈ Ioc a b, D.laplacian (fun y => G y t) x ≤ G' x t)
    (hboundary : ∀ x ∈ closure Ω, x ∉ Ω → ∀ t ∈ Icc a b, F x t ≤ G x t)
    (hinit : ∀ x ∈ closure Ω, F x a ≤ G x a) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b, F x t ≤ G x t := by
  have h := nonpos_of_subsolution D hΩ hc (F := fun x t => F x t - G x t)
    (F' := fun x t => F' x t - G' x t) (K := 0) (hF.sub hG)
    (fun t ht => (hFs t ht).sub (hGs t ht))
    (fun x hx t ht => (hFd x hx t ht).sub (hGd x hx t ht))
    (fun x hx t ht => ?_)
    (fun x hx hxo t ht => sub_nonpos.mpr (hboundary x hx hxo t ht))
    (fun x hx => sub_nonpos.mpr (hinit x hx))
  · exact fun x hx t ht => sub_nonpos.mp (h x hx t ht)
  · rw [laplacian_sub_on D hΩ (hFs t ht) (hGs t ht) hx, zero_mul, add_zero]
    exact sub_le_sub (hsub x hx t ht) (hsuper x hx t ht)

theorem eq_of_heat_equation
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    (hc : IsCompact (closure Ω)) {F G : M → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (closure Ω ×ˢ Icc a b))
    (hG : ContinuousOn (Function.uncurry G) (closure Ω ×ˢ Icc a b))
    (hFs : ∀ t ∈ Ioc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => F x t) Ω)
    (hGs : ∀ t ∈ Ioc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => G x t) Ω)
    (hFd : ∀ x ∈ Ω, ∀ t ∈ Ioc a b,
      HasDerivWithinAt (F x) (D.laplacian (fun y => F y t) x) (Icc a b) t)
    (hGd : ∀ x ∈ Ω, ∀ t ∈ Ioc a b,
      HasDerivWithinAt (G x) (D.laplacian (fun y => G y t) x) (Icc a b) t)
    (hboundary : ∀ x ∈ closure Ω, x ∉ Ω → ∀ t ∈ Icc a b, F x t = G x t)
    (hinit : ∀ x ∈ closure Ω, F x a = G x a) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b, F x t = G x t := by
  have hle := le_of_subsolution_supersolution D hΩ hc hF hG hFs hGs hFd hGd
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (fun x hx hxo t ht => (hboundary x hx hxo t ht).le) (fun x hx => (hinit x hx).le)
  have hge := le_of_subsolution_supersolution D hΩ hc hG hF hGs hFs hGd hFd
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (fun x hx hxo t ht => (hboundary x hx hxo t ht).ge) (fun x hx => (hinit x hx).ge)
  exact fun x hx t ht => le_antisymm (hle x hx t ht) (hge x hx t ht)

end PoincareConjecture.LeviCivitaData.Dirichlet
