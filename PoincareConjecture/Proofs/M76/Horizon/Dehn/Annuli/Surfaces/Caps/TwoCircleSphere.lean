import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CircleIncidence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.TwoCapLinks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CountTwoSphere

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V2" => (Fin 2 → ℝ)

open Classical in

theorem exists_two_circle_capped_sphere
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hzero : K.surfaceEulerCount = 0)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ b, L b ≤ K)
    (gamma : ∀ b, sphere (0 : V2) 1 ≃ₜ (L b).space)
    (hgamma : ∀ b, (gamma b).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ b, s ∈ (L b).faces then 1 else 2) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧
      J.space = ((fun x : E ↦ (x, (0 : ℝ))) '' K.space ∪
        boundaryCircleCap false (L false).space) ∪ boundaryCircleCap true (L true).space ∧
      ∃ H : J.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL := by
  classical
  have hL (b : Bool) : (L b).faces.Finite := hK.subset (hLK b)
  have hinc (b : Bool) := circle_incidence (L b) (hL b) (gamma b) (hgamma b)
  have hdim (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    obtain ⟨t, ht, hc, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq hc
  obtain ⟨J, hJ, hJs, _, hcount, _, hfaces⟩ := exists_two_cap_triangulation_with_faces
    K hK hdim L hLK (fun b ↦ (hinc b).2.2.1.nonempty) (fun b ↦ (hinc b).1) hdis
  have hpureJ := two_cap_pure K L J hfaces hpure (fun b ↦ (hinc b).2.1)
    (fun b ↦ (hinc b).2.2.1.nonempty)
  have hedgeJ := two_cap_two_triangle_cofaces K L J hfaces hdis hboundary
    (fun b ↦ (hinc b).2.2.2.1)
  have hlinksJ := two_cap_links_isConnected K L J hfaces hpure hLK
    (fun b ↦ (hinc b).2.1) (fun b ↦ (hinc b).2.2.1) hlinks
  have hcountJ : J.surfaceEulerCount = 2 := by
    simpa only [hzero, (hinc false).2.2.2.2, (hinc true).2.2.2.2, sub_zero, zero_add]
      using hcount
  have hcap (b : Bool) : IsConnected (boundaryCircleCap b (L b).space) :=
    (isFinitePLBallPair_boundaryCircleCap b (gamma b) (hgamma b)).isConnected
  have hmeet (b : Bool) : (((fun x : E ↦ (x, (0 : ℝ))) '' K.space) ∩
      boundaryCircleCap b (L b).space).Nonempty := by
    obtain ⟨v, hv⟩ := (hinc b).2.2.1.nonempty
    refine ⟨(v, 0), mem_image_of_mem _ (SimplicialComplex.space_subset_of_le (hLK b) hv), ?_⟩
    apply (mem_boundaryCircleCap_iff b (L b).space (v, 0)).mpr
    exact ⟨v, hv, 1, by norm_num, by simp⟩
  have hconnJ : IsConnected J.space := by
    rw [hJs]
    have hbase := hconn.image (fun x : E ↦ (x, (0 : ℝ)))
      (continuous_id.prodMk continuous_const).continuousOn
    have hfirst := IsConnected.union (hmeet false) hbase (hcap false)
    apply IsConnected.union _ hfirst (hcap true)
    obtain ⟨x, hx, hxc⟩ := hmeet true
    exact ⟨x, Or.inl hx, hxc⟩
  exact ⟨J, hJ, hJs, J.exists_sphere_model_of_surfaceEulerCount_eq_two hJ
    hpureJ hedgeJ hlinksJ hconnJ hcountJ⟩

end PoincareConjecture.M76.Dehn.Annuli
