import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryLinks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CircleIncidence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CountTwoSphere

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem exists_one_boundary_capped_sphere
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hcount : K.surfaceEulerCount = 1) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧
      J.space = (fun x : E ↦ (x, (0 : ℝ))) '' K.space ∪ boundaryCircleCap true L.space ∧
      ∃ H : J.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL := by
  classical
  have hinc := circle_incidence L (hK.subset hLK) gamma hgamma
  obtain ⟨J, hJ, hJs, hcountJ, hfaces⟩ := exists_one_boundary_cap_triangulation
    K L hK hLK hinc.2.2.1.nonempty hinc.1
  have hpJ := one_boundary_cap_pure K L J hfaces hpure hinc.2.1 hinc.2.2.1.nonempty
  have heJ := one_boundary_cap_two_cofaces K L J hfaces hboundary hinc.2.2.2.1
  have hlJ := one_boundary_cap_links_connected K L J hfaces hpure hLK
    hinc.2.1 hinc.2.2.1 hlinks
  have hcount2 : J.surfaceEulerCount = 2 := by
    simpa only [hcount, hinc.2.2.2.2, sub_zero, show (1 : ℤ) + 1 = 2 from rfl]
      using hcountJ
  have hconnJ : IsConnected J.space := by
    rw [hJs]
    have hc := (isFinitePLBallPair_boundaryCircleCap true gamma hgamma).isConnected
    have hb := hconn.image (fun x : E ↦ (x, (0 : ℝ)))
      (continuous_id.prodMk continuous_const).continuousOn
    apply IsConnected.union _ hb hc
    obtain ⟨v, hv⟩ := hinc.2.2.1.nonempty
    refine ⟨(v, 0), mem_image_of_mem _ (SimplicialComplex.space_subset_of_le hLK hv), ?_⟩
    exact (mem_boundaryCircleCap_iff true L.space _).mpr
      ⟨v, hv, 1, by norm_num, by simp⟩
  exact ⟨J, hJ, hJs, J.exists_sphere_model_of_surfaceEulerCount_eq_two hJ
    hpJ heJ hlJ hconnJ hcount2⟩

end PoincareConjecture.M76.Dehn.Annuli
