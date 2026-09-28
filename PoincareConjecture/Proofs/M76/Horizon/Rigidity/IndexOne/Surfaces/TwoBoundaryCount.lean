import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CappedEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.PartialCapIncidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.Capping.FiniteCap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryLinks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CircleIncidence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.CountZeroAnnulus



set_option autoImplicit false
open Set Metric Geometry BrownCollar PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

open Dehn.Annuli

open Classical in
theorem surfaceEulerCount_eq_zero_of_generating_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsPathConnected K.space)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ side, L side ≤ K)
    (gamma : ∀ side, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L side).space)
    (hgamma : ∀ side, (gamma side).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ side, s ∈ (L side).faces then 1 else 2)
    (b : (L false).space)
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (hLK false))) b))
    (hlocal : ∀ x : (L false).space,
      ∃ c : OpenPartialHomeomorph ((L false).space × Ico (0 : ℝ) 1) K.space,
        collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
          c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le (hLK false)) a) :
    K.surfaceEulerCount = 0 := by
  have hinc (side : Bool) := circle_incidence (L side) (hK.subset (hLK side))
    (gamma side) (hgamma side)
  have hbd (s : Finset E) (hs : s ∈ K.faces) (hsc : s.card = 2) :
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ (L false).faces ∨ s ∈ (L true).faces then 1 else 2 := by
    simpa only [Bool.exists_bool] using hboundary s hs hsc
  obtain ⟨J, hJ, hJs, hcountJ, hfaces⟩ := exists_one_boundary_cap_triangulation
    K (L false) hK (hLK false) (hinc false).2.2.1.nonempty (hinc false).1
  have hpJ := one_boundary_cap_pure K (L false) J hfaces hpure
    (hinc false).2.1 (hinc false).2.2.1.nonempty
  have heJ := one_boundary_cap_cofaces_le_two_of_two_rims K (L false) J hfaces
    (L true) hdis hbd (hinc false).2.2.2.1
  have hlJ := one_boundary_cap_links_connected K (L false) J hfaces hpure (hLK false)
    (hinc false).2.1 (hinc false).2.2.1 hlinks
  have hboundaryJ : ∃ e ∈ J.faces, e.card = 2 ∧
      {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 1 := by
    obtain ⟨x, hx⟩ := (hinc true).2.2.1.nonempty
    obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨e, he, hec, _⟩ := (hinc true).2.1 s hs
    let z : E → E × ℝ := fun x => (x, 0)
    refine ⟨e.image z, (hfaces _).mpr (Or.inl ⟨e, hLK true he, rfl⟩), ?_, ?_⟩
    · rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.fst h)]
      exact hec
    · have h := one_boundary_cap_base_cofaces_count_two_rims K (L false) J hfaces
        (L true) hdis e hec (hbd e (hLK true he) hec)
      simpa only [he, if_true] using h
  have hcap := isSimplyConnected_finite_boundaryCircleCap K (L false) hK (hLK false)
    hconn (gamma false) (hgamma false) b hgenerate hlocal
  let : SimplyConnectedSpace J.space := hJs.symm ▸ hcap
  have hone := surfaceEulerCount_eq_one_of_simplyConnected_boundary J hJ hpJ heJ hlJ hboundaryJ
  rw [(hinc false).2.2.2.2, sub_zero] at hcountJ
  omega

open Classical in
theorem exists_annulus_of_generating_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsPathConnected K.space)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ side, L side ≤ K)
    (gamma : ∀ side, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L side).space)
    (hgamma : ∀ side, (gamma side).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ side, s ∈ (L side).faces then 1 else 2)
    (b : (L false).space)
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (hLK false))) b))
    (hlocal : ∀ x : (L false).space,
      ∃ c : OpenPartialHomeomorph ((L false).space × Ico (0 : ℝ) 1) K.space,
        collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
          c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le (hLK false)) a) :
    ∃ A : squareAnnulus 8 1 ≃ₜ K.space, A.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔ (A p : E) ∈ (L false).space) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔ (A p : E) ∈ (L true).space) := by
  exact exists_annulus_of_count_zero K hK hpure hlinks hconn.isConnected
    (surfaceEulerCount_eq_zero_of_generating_boundary K hK hpure hlinks hconn L hLK
      gamma hgamma hdis hboundary b hgenerate hlocal) L hLK gamma hgamma hdis hboundary

end PoincareConjecture.M76.HamiltonIntervalTorus
