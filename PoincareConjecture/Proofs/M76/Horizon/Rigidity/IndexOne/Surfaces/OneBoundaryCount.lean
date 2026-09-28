import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CappedEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.Capping.FiniteCap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundarySphere
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryDisk



set_option autoImplicit false
open Set Metric Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

open Dehn.Annuli

open Classical in
theorem surfaceEulerCount_eq_one_of_generating_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsPathConnected K.space) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2)
    (b : L.space)
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)) b))
    (hlocal : ∀ x : L.space,
      ∃ c : OpenPartialHomeomorph (L.space × Ico (0 : ℝ) 1) K.space,
        collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
          c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le hLK) a) :
    K.surfaceEulerCount = 1 := by
  have hinc := circle_incidence L (hK.subset hLK) gamma hgamma
  obtain ⟨J, hJ, hJs, hcountJ, hfaces⟩ := exists_one_boundary_cap_triangulation
    K L hK hLK hinc.2.2.1.nonempty hinc.1
  have hpJ := one_boundary_cap_pure K L J hfaces hpure hinc.2.1 hinc.2.2.1.nonempty
  have heJ := one_boundary_cap_two_cofaces K L J hfaces hboundary hinc.2.2.2.1
  have hlJ := one_boundary_cap_links_connected K L J hfaces hpure hLK
    hinc.2.1 hinc.2.2.1 hlinks
  have hcap := isSimplyConnected_finite_boundaryCircleCap K L hK hLK hconn
    gamma hgamma b hgenerate hlocal
  let : SimplyConnectedSpace J.space := hJs.symm ▸ hcap
  have htwo := surfaceEulerCount_eq_two_of_simplyConnected J hJ hpJ heJ hlJ
  rw [hinc.2.2.2.2, sub_zero] at hcountJ
  omega

open Classical in
theorem isFinitePLBallPair_of_generating_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsPathConnected K.space) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2)
    (b : L.space)
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)) b))
    (hlocal : ∀ x : L.space,
      ∃ c : OpenPartialHomeomorph (L.space × Ico (0 : ℝ) 1) K.space,
        collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
          c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le hLK) a) :
    IsFinitePLBallPair (ℝ × ℝ) K.space L.space := by
  exact isFinitePLBallPair_of_one_boundary_count_one K L hK hpure hlinks hconn.isConnected
    (surfaceEulerCount_eq_one_of_generating_boundary K L hK hpure hlinks hconn hLK
      gamma hgamma hboundary b hgenerate hlocal) hLK gamma hgamma hboundary

end PoincareConjecture.M76.HamiltonIntervalTorus
