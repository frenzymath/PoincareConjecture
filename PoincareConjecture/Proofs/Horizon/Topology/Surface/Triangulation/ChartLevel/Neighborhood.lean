import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.TransverseLevels

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]

theorem finite_complement_chart_image
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {p : M} {W B : Set (EuclideanSpace ℝ (Fin 2))} {A s : Set M}
    (hp : p ∈ c.source) (hW : IsOpen W) (hpW : c p ∈ W)
    (htarget : W ⊆ c.target)
    (hlocal : ∀ z ∈ W, c.symm z ∈ A ↔ z ∈ B)
    (hsub : W ⊆ c.symm ⁻¹' s)
    (hfinite : Finite (ConnectedComponents ((W \ B) : Set (EuclideanSpace ℝ (Fin 2))))) :
    IsOpen (c.symm '' W) ∧ p ∈ c.symm '' W ∧ c.symm '' W ⊆ s ∧
      Finite (ConnectedComponents (((c.symm '' W) \ A) : Set M)) := by
  have hdiff : c.symm '' (W \ B) = (c.symm '' W) \ A := by
    ext x
    constructor
    · rintro ⟨z, ⟨hzW, hzB⟩, rfl⟩
      exact ⟨⟨z, hzW, rfl⟩, fun h => hzB ((hlocal z hzW).mp h)⟩
    · rintro ⟨⟨z, hzW, rfl⟩, hzA⟩
      exact ⟨z, ⟨hzW, fun h => hzA ((hlocal z hzW).mpr h)⟩, rfl⟩
  refine ⟨c.isOpen_image_symm_of_subset_target hW htarget,
    ⟨c p, hpW, c.left_inv hp⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hsub hz
  · have := hfinite
    rw [← hdiff]
    exact Poincare.Topology.finite_connectedComponents_image_of_continuousOn
      (c.continuousOn_symm.mono (sdiff_subset.trans htarget))

theorem exists_finite_complement_chart_regular_level
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {p : M} (hp : p ∈ c.source)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiffAt ℝ ∞ f (c p)) (hdf : fderiv ℝ f (c p) ≠ 0)
    {A s : Set M} {N : Set (EuclideanSpace ℝ (Fin 2))}
    (hN : N ∈ 𝓝 (c p))
    (hlocal : ∀ z ∈ N, c.symm z ∈ A ↔ f z = f (c p))
    (hs : s ∈ 𝓝 p) :
    ∃ Z : Set M, IsOpen Z ∧ p ∈ Z ∧ Z ⊆ s ∧
      Finite (ConnectedComponents ((Z \ A) : Set M)) := by
  have htarget := c.map_source hp
  have hnbhd : N ∩ (c.target ∩ c.symm ⁻¹' s) ∈ 𝓝 (c p) := by
    refine Filter.inter_mem hN (Filter.inter_mem (c.open_target.mem_nhds htarget) ?_)
    apply (c.continuousAt_symm htarget).preimage_mem_nhds
    simpa only [c.left_inv hp] using hs
  obtain ⟨W, hW, hpW, hsub, hfinite⟩ :=
    Poincare.Topology.Plane.Curves.exists_finite_complement_of_regular_level hf hdf hnbhd
  refine ⟨c.symm '' W, finite_complement_chart_image c hp hW hpW
    (fun z hz => (hsub hz).2.1) ?_ (fun z hz => (hsub hz).2.2) hfinite⟩
  intro z hz
  exact hlocal z (hsub hz).1

theorem exists_finite_complement_chart_transverse_levels
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {p : M} (hp : p ∈ c.source)
    {f g : EuclideanSpace ℝ (Fin 2) → ℝ} {v : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f (c p)) (hg : ContDiffAt ℝ ∞ g (c p))
    (hdf : fderiv ℝ f (c p) ≠ 0)
    (hvf : fderiv ℝ f (c p) v = 0) (hvg : fderiv ℝ g (c p) v ≠ 0)
    {A s : Set M} {N : Set (EuclideanSpace ℝ (Fin 2))}
    (hN : N ∈ 𝓝 (c p))
    (hlocal : ∀ z ∈ N, c.symm z ∈ A ↔ f z = f (c p) ∨ g z = g (c p))
    (hs : s ∈ 𝓝 p) :
    ∃ Z : Set M, IsOpen Z ∧ p ∈ Z ∧ Z ⊆ s ∧
      Finite (ConnectedComponents ((Z \ A) : Set M)) := by
  have htarget := c.map_source hp
  have hnbhd : N ∩ (c.target ∩ c.symm ⁻¹' s) ∈ 𝓝 (c p) := by
    refine Filter.inter_mem hN (Filter.inter_mem (c.open_target.mem_nhds htarget) ?_)
    apply (c.continuousAt_symm htarget).preimage_mem_nhds
    simpa only [c.left_inv hp] using hs
  obtain ⟨W, hW, hpW, hsub, hfinite⟩ :=
    Poincare.Topology.Plane.Curves.exists_finite_complement_of_transverse_levels
      hf hg hdf hvf hvg hnbhd
  refine ⟨c.symm '' W, finite_complement_chart_image c hp hW hpW
    (fun z hz => (hsub hz).2.1) ?_ (fun z hz => (hsub hz).2.2) hfinite⟩
  intro z hz
  exact hlocal z (hsub hz).1

end PoincareConjecture.Topology.Surface
