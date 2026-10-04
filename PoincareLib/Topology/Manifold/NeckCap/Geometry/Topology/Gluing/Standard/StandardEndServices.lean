import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Buffered.BufferedCollar
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Standard.StandardEnd

/-!
# Standard radial ends from the explicit topology services

Fixed buffered levels and the actual normalized collar let the two
assumed topology services supply the inputs to the global standard-end
assembly. The actual cofinal upper end, both smooth directions, and one
orthogonal sphere map are retained. This is the service wrapper for
Morgan--Tian A.21, pp. 510-514; see
`tasks/M25/gluing-collar/standard-end-services-plan.md`, section 3.
Neither topology service is proved by this file.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D

/-- The two explicit topology services straighten an actual cofinal
cylinder end with a literal positive radial formula and the same
orthogonal map at every retained height. The radial chart has an actual
smooth inverse on its exact positive target. StandardEnd services plan,
section 3, for MT A.21, pp. 510-514. -/
theorem standardEnd_of_openPartialHomeomorph
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {W : Type u} [TopologicalSpace W] [ChartedSpace E3 W]
    [IsManifold (𝓡 3) ∞ W]
    (Phi0 : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞)
    (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) W)
    {a b c η : ℝ}
    (hsource : e.source = univ ×ˢ Ioo a b)
    (he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hc : c ∈ Ioo a b) (hη : 0 < η) (hcb : c + η < b) :
    ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞) (A : E3 ≃ₗᵢ[ℝ] E3)
      (r0 : ℝ) (sigma : OpenPartialHomeomorph ℝ ℝ),
      0 < r0 ∧ sigma.source = Ioo (c + η) b ∧ sigma.target = Ioi r0 ∧
      ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source ∧
      ContDiffOn ℝ ∞ sigma.symm sigma.target ∧
      StrictMonoOn (sigma : ℝ → ℝ) sigma.source ∧
      (∀ s ∈ sigma.source, 0 < deriv (sigma : ℝ → ℝ) s) ∧
      (∀ q : UnitTwoSphere, ∀ s ∈ Ioo (c + η) b,
        Phi (e (q, s)) = sigma s • (sphereMap A q).1) := by
  let h := min ((c - a) / 2) (min (η / 2) ((b - c) / 2))
  have hh : 0 < h := by
    dsimp only [h]
    apply lt_min
    · linarith [hc.1]
    · apply lt_min <;> linarith [hc.2]
  have hleft : h ≤ (c - a) / 2 := min_le_left _ _
  have hgap : h ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hright : h ≤ (b - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have ha : a < c - h := by linarith [hc.1]
  have hb : c + h < b := by linarith [hc.2]
  have hv : c + η ∈ Ico (c + h * (3 / 4)) b := ⟨by linarith, hcb⟩
  have hEmbedding : IsCollarEmbedding (fun p => Phi0 (e (p.1, c + h * p.2))) :=
    isCollarEmbedding_of_buffered_chart Phi0 e hsource he hei hh ha hb
  obtain ⟨S⟩ := hS (fun p => Phi0 (e (p.1, c + h * p.2))) hEmbedding
    (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨D⟩ := hD S.boundary_map
  obtain ⟨Phi, r0, sigma, hresult⟩ :=
    S.exists_standardEnd_of_data (tl := 1 / 4) (tm := 1 / 2) (tu := 3 / 4)
      Phi0 e D hsource he hei hend hEmbedding hh ha hb
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv
  exact ⟨Phi, D.isometry, r0, sigma, hresult⟩

end PoincareMT.M25.Topology3D
