import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurgeryData














set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_regular_surgery_data_of_tube (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t d : ℝ) (hd : 0 < d)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hTs : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hTm : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hTh : ∀ p : E2 × ℝ, ⟪(u : E3), T p⟫_ℝ = p.2)
    (hmem : ∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
      T (x, z) ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) ↔ x ∈ sphere 0 1) :
    ∃ D : RegularSurgeryData ψ u t, D.width = d ∧ D.tube = T := by
  have hbd : sphere (0 : E2) 1 ×ˢ Ioo (t - d) (t + d) ⊆ T.source :=
    fun _ hp => hTs ⟨sphere_subset_closedBall hp.1, mem_univ _⟩
  have hsurface (θ : UnitCircle) (z : ℝ) (hz : z ∈ Ioo (t - d) (t + d)) :
      T (θ.1, z) ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) :=
    (hmem θ.1 (sphere_subset_closedBall θ.2) z hz).mpr θ.2
  obtain ⟨Q, hQs, hQm, hQi, hrec⟩ :=
    exists_source_tube_chart ψ hψ T hTm hTi isOpen_Ioo hbd hsurface
  obtain ⟨C, hCs, hCm, hCi, hC⟩ :=
    exists_centered_source_collar Q hQm hQi t d hQs
  have hCrec (θ : UnitCircle) (s : ℝ) (hs : s ∈ Ioo (-d) d) :
      ψ (C (θ, s), 0) = T (θ.1, t + s) := by
    rw [hC]
    exact hrec θ (t + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlevel (θ : UnitCircle) : ⟪(u : E3), ψ (C (θ, 0), 0)⟫_ℝ = t := by
    rw [hCrec θ 0 ⟨neg_neg_of_pos hd, hd⟩, hTh, add_zero]
  obtain ⟨θ₀⟩ : Nonempty UnitCircle :=
    (NormedSpace.sphere_nonempty (E := E2) (x := 0) |>.mpr zero_le_one).coe_sort
  let v : UnitTwoSphere := C (θ₀, d / 2)
  have hvheight : ⟪(u : E3), ψ (v, 0)⟫_ℝ = t + d / 2 := by
    change ⟪(u : E3), ψ (C (θ₀, d / 2), 0)⟫_ℝ = _
    rw [hCrec θ₀ (d / 2) ⟨by linarith, by linarith⟩, hTh]
  have hvC : v ∉ range (fun θ : UnitCircle => C (θ, 0)) := by
    rintro ⟨θ, hθ⟩
    have hvzero : ⟪(u : E3), ψ (v, 0)⟫_ℝ = t := hθ ▸ hlevel θ
    linarith
  obtain ⟨D⟩ := exists_rectified_source_disc_pair hP C hCm hCi hd hCs v hvC
    (show 0 < d / 2 by positivity)
  exact ⟨{
    width := d
    width_pos := hd
    tube := T
    tube_source := hTs
    tube_smooth := hTm
    tube_inverse := hTi
    tube_height := hTh
    surface_mem := hmem
    sourceCollar := C
    sourceCollar_source := hCs
    sourceCollar_smooth := hCm
    sourceCollar_inverse := hCi
    reconstruction := hCrec
    sourceDiscs := D }, rfl, rfl⟩

end PoincareConjecture.M25.Topology3D
