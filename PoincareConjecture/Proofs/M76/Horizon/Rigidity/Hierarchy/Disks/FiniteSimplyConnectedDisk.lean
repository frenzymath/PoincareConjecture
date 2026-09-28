import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.PolygonCircleModels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CappedEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.BoundaryEulerBound

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

open Classical in
theorem isFinitePLBallPair_of_simplyConnected_marked_surface
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hBK : B ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ B.faces then 1 else 2)
    (hpolygons : HasDisjointPolygonPresentation B.space) (hBne : B.space.Nonempty)
    [SimplyConnectedSpace K.space] :
    IsFinitePLBallPair (ℝ × ℝ) K.space B.space := by
  classical
  obtain ⟨m, L, gamma, hL, hdis, hcover, hfaces⟩ :=
    B.exists_circle_subcomplexes_of_polygon_presentation (hK.subset hBK) hpolygons
  obtain ⟨z, hz⟩ := hBne
  have hzcover : z ∈ ⋃ i, (L i).space := hcover.symm ▸ hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzcover
  have hinc := Dehn.Annuli.circle_incidence (L i) (hL i).2.1 (gamma i) (hL i).2.2
  obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp hi
  obtain ⟨t, ht, htc, _⟩ := hinc.2.1 s hs
  have htB : t ∈ B.faces := (hL i).1 ht
  have hboundary : ∃ t ∈ K.faces, t.card = 2 ∧
      {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 1 := by
    refine ⟨t, hBK htB, htc, ?_⟩
    simpa only [if_pos htB] using hcofaces t (hBK htB) htc
  have hcount := HamiltonIntervalTorus.surfaceEulerCount_eq_one_of_simplyConnected_boundary
    K hK hpure (fun t ht htc => by rw [hcofaces t ht htc]; split_ifs <;> omega)
    hlinks hboundary
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have hle := K.surfaceEulerCount_le_two_sub_boundary_circle_count
    hK hpure hconn hlinks L (fun j => (hL j).1.trans hBK)
    hdis gamma (fun j => (hL j).2.2)
    (fun t ht htc => by simpa only [← hfaces] using hcofaces t ht htc)
  have hm : m = 1 := by
    simp only [Nat.card_fin, hcount] at hle
    have := i.isLt
    omega
  have honly (j : Fin m) : j = i := by
    apply Fin.ext
    have := j.isLt
    have := i.isLt
    omega
  have hLi : (L i).space = B.space := by
    rw [← hcover]
    ext y
    simp only [mem_iUnion]
    exact ⟨fun h => ⟨i, h⟩, fun ⟨j, hj⟩ => honly j ▸ hj⟩
  have hface (t : Finset E) : t ∈ B.faces ↔ t ∈ (L i).faces := by
    rw [hfaces]
    exact ⟨fun ⟨j, hj⟩ => honly j ▸ hj, fun h => ⟨i, h⟩⟩
  have hball := Dehn.Annuli.isFinitePLBallPair_of_one_boundary_count_one
    K (L i) hK hpure hlinks hconn hcount ((hL i).1.trans hBK)
    (gamma i) (hL i).2.2
    (fun t ht htc => by simpa only [hface] using hcofaces t ht htc)
  rwa [hLi] at hball

end PoincareConjecture.M76
