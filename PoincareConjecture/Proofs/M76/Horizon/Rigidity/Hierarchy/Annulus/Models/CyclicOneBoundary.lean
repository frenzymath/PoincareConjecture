import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CapOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.CyclicSurfaceEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComponentParity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryDisk









set_option autoImplicit false
open Set Metric Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Dehn.Annuli

open Classical in
theorem surfaceEulerCount_eq_one_of_isCyclic_and_one_oriented_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    K.surfaceEulerCount = 1 := by
  have hlo := K.surfaceEulerCount_nonneg_of_isCyclic hK hconn x
  have hhi : K.surfaceEulerCount ≤ 1 := by
    simpa using K.surfaceEulerCount_le_two_sub_boundary_circle_count
      hK hpure hconn hlinks (fun _ : Unit => L) (fun _ => hLK)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      (fun _ => gamma) (fun _ => hgamma)
      (by intro s hs hsc; simpa using hboundary s hs hsc)
  have hinc := circle_incidence L (hK.subset hLK) gamma hgamma
  obtain ⟨J, hJ, _, hcountJ, hfaces⟩ := exists_one_boundary_cap_triangulation
    K L hK hLK hinc.2.2.1.nonempty hinc.1
  have hpJ := one_boundary_cap_pure K L J hfaces hpure hinc.2.1 hinc.2.2.1.nonempty
  have heJ := one_boundary_cap_two_cofaces K L J hfaces hboundary hinc.2.2.2.1
  have hlJ := one_boundary_cap_links_connected K L J hfaces hpure hLK
    hinc.2.1 hinc.2.2.1 hlinks
  obtain ⟨label, sigma, hlabel, hsigma⟩ := exists_one_boundary_cap_geometric_signs
    K L J hK hLK hfaces hlinks
    (by intro s hs hsc; simpa only [if_pos hs] using hboundary s (hLK hs) hsc)
    number hnumber sign hcancel
  obtain ⟨n, hn⟩ := J.even_surfaceEulerCount_of_geometric_signs hJ hpJ
    (by intro v hv; convert! hlJ v hv) heJ
    label hlabel sigma (by convert! hsigma)
  rw [hinc.2.2.2.2, sub_zero] at hcountJ
  omega

open Classical in
theorem isFinitePLBallPair_of_isCyclic_and_one_oriented_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    IsFinitePLBallPair (ℝ × ℝ) K.space L.space := by
  exact isFinitePLBallPair_of_one_boundary_count_one K L hK hpure hlinks hconn
    (surfaceEulerCount_eq_one_of_isCyclic_and_one_oriented_boundary K L hK hpure
      hlinks hconn hLK gamma hgamma hboundary number hnumber sign hcancel x)
    hLK gamma hgamma hboundary

end PoincareConjecture.M76
