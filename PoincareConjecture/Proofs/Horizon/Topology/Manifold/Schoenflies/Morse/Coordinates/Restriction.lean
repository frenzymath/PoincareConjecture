import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M]

theorem exists_restricted_morse_coordinates_of_eventuallyEq_add_const
    {h g : M -> Real} {p : M} {c : Real}
    (e : OpenPartialHomeomorph E2 M) (sigma : Fin 2 -> Real)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source,
      h (e x) = h p + ∑ i : Fin 2, sigma i * x i ^ 2)
    (hg : g =ᶠ[𝓝 p] fun q => h q + c) :
    ∃ d : OpenPartialHomeomorph E2 M,
      0 ∈ d.source ∧ d 0 = p ∧ d.source ⊆ e.source ∧
      (∀ x, d x = e x) ∧ (∀ q, d.symm q = e.symm q) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      ∀ x ∈ d.source, g (d x) = g p + ∑ i : Fin 2, sigma i * x i ^ 2 := by
  have hecont : ContinuousAt e 0 := e.continuousOn.continuousAt
    (e.open_source.mem_nhds he0)
  have hlocal : (fun x => g (e x)) =ᶠ[𝓝 (0 : E2)] (fun x => h (e x) + c) :=
    hg.comp_tendsto (hep ▸ hecont)
  obtain ⟨s, hs, hsopen, hs0⟩ := _root_.mem_nhds_iff.mp hlocal
  let d := e.restrOpen s hsopen
  refine ⟨d, ⟨he0, hs0⟩, hep, inter_subset_left, (fun _ => rfl),
    (fun _ => rfl), he.mono inter_subset_left, hei.mono inter_subset_left, ?_⟩
  intro x hx
  change g (e x) = g p + ∑ i : Fin 2, sigma i * x i ^ 2
  have hxg : g (e x) = h (e x) + c := hs hx.2
  have hpg : g p = h p + c := hg.eq_of_nhds
  rw [hxg, hform x hx.1, hpg]
  ring

theorem morse_coordinates_of_eventuallyEq_add_const_at_critical_points
    {h g : M -> Real}
    (hcoordinates : ∀ p : M, mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 ->
      ∃ (e : OpenPartialHomeomorph E2 M) (sigma : Fin 2 -> Real),
        (∀ i, sigma i = -1 ∨ sigma i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        ∀ x ∈ e.source, h (e x) = h p + ∑ i : Fin 2, sigma i * x i ^ 2)
    (hcritical : ∀ p : M, mfderiv (𝓡 2) 𝓘(Real, Real) g p = 0 ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0)
    (hlocal : ∀ p : M, mfderiv (𝓡 2) 𝓘(Real, Real) g p = 0 ->
      ∃ c : Real, g =ᶠ[𝓝 p] fun q => h q + c) :
    ∀ p : M, mfderiv (𝓡 2) 𝓘(Real, Real) g p = 0 ->
      ∃ (e : OpenPartialHomeomorph E2 M) (sigma : Fin 2 -> Real),
        (∀ i, sigma i = -1 ∨ sigma i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        ∀ x ∈ e.source, g (e x) = g p + ∑ i : Fin 2, sigma i * x i ^ 2 := by
  intro p hp
  obtain ⟨e, sigma, hsigma, he0, hep, he, hei, hform⟩ :=
    hcoordinates p (hcritical p hp)
  obtain ⟨c, hc⟩ := hlocal p hp
  obtain ⟨d, hd0, hdp, _, _, _, hd, hdi, hdform⟩ :=
    exists_restricted_morse_coordinates_of_eventuallyEq_add_const
      e sigma he0 hep he hei hform hc
  exact ⟨d, sigma, hsigma, hd0, hdp, hd, hdi, hdform⟩

end Poincare.Manifold.Schoenflies
