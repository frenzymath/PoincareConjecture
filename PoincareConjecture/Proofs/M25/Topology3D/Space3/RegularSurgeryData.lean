import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularInnermostTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCirclePullback
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCollarTranslation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceRectifiedPair

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

structure RegularSurgeryData (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) (t : ℝ) where
  width : ℝ
  width_pos : 0 < width
  tube : OpenPartialHomeomorph (E2 × ℝ) E3
  tube_source : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ tube.source
  tube_smooth : ContDiffOn ℝ ∞ tube tube.source
  tube_inverse : ContDiffOn ℝ ∞ tube.symm tube.target
  tube_height : ∀ p : E2 × ℝ, ⟪(u : E3), tube p⟫_ℝ = p.2
  surface_mem : ∀ p ∈ closedBall (0 : E2) 1, ∀ z ∈ Ioo (t - width) (t + width),
    tube (p, z) ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) ↔ p ∈ sphere 0 1
  sourceCollar : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere
  sourceCollar_source : sourceCollar.source = univ ×ˢ Ioo (-width) width
  sourceCollar_smooth :
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ sourceCollar sourceCollar.source
  sourceCollar_inverse :
    ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ sourceCollar.symm sourceCollar.target
  reconstruction : ∀ θ : UnitCircle, ∀ s ∈ Ioo (-width) width,
    ψ (sourceCollar (θ, s), 0) = tube (θ.1, t + s)
  sourceDiscs : RectifiedSourceDiscPair sourceCollar width (width / 2)

theorem exists_regular_surgery_data (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x₀ : collarHeightLevel ψ (u : E3) t) : Nonempty (RegularSurgeryData ψ u t) := by
  obtain ⟨_, d, hd, e, hes, hem, hei, heh, _, hmem⟩ :=
    exists_regular_collar_innermost_tube hP ψ hψ u t hreg x₀
  have hbd : sphere (0 : E2) 1 ×ˢ Ioo (t - d) (t + d) ⊆ e.source :=
    fun _ hp => hes ⟨sphere_subset_closedBall hp.1, mem_univ _⟩
  have hsurface (θ : UnitCircle) (z : ℝ) (hz : z ∈ Ioo (t - d) (t + d)) :
      e (θ.1, z) ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) :=
    (hmem θ.1 (sphere_subset_closedBall θ.2) z hz).mpr θ.2
  obtain ⟨Q, hQs, hQm, hQi, hrec⟩ :=
    exists_source_tube_chart ψ hψ e hem hei isOpen_Ioo hbd hsurface
  obtain ⟨C, hCs, hCm, hCi, hC⟩ :=
    exists_centered_source_collar Q hQm hQi t d hQs
  have hCrec (θ : UnitCircle) (s : ℝ) (hs : s ∈ Ioo (-d) d) :
      ψ (C (θ, s), 0) = e (θ.1, t + s) := by
    rw [hC]
    exact hrec θ (t + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlevel (θ : UnitCircle) : ⟪(u : E3), ψ (C (θ, 0), 0)⟫_ℝ = t := by
    rw [hCrec θ 0 ⟨neg_neg_of_pos hd, hd⟩, heh, add_zero]
  obtain ⟨θ₀⟩ : Nonempty UnitCircle :=
    (NormedSpace.sphere_nonempty (E := E2) (x := 0) |>.mpr zero_le_one).coe_sort
  obtain ⟨v, hv⟩ := exists_pole_off_regular_height
    (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) t (C (θ₀, 0))
    (hreg _ (hlevel θ₀))
  have hvC : v ∉ range (fun θ : UnitCircle => C (θ, 0)) := by
    rintro ⟨θ, hθ⟩
    exact hv (hθ ▸ hlevel θ)
  obtain ⟨D⟩ := exists_rectified_source_disc_pair hP C hCm hCi hd hCs v hvC
    (show 0 < d / 2 by positivity)
  exact ⟨{
    width := d
    width_pos := hd
    tube := e
    tube_source := hes
    tube_smooth := hem
    tube_inverse := hei
    tube_height := heh
    surface_mem := hmem
    sourceCollar := C
    sourceCollar_source := hCs
    sourceCollar_smooth := hCm
    sourceCollar_inverse := hCi
    reconstruction := hCrec
    sourceDiscs := D }⟩

end PoincareConjecture.M25.Topology3D
