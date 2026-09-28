import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryArcBoundary
import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryEndpointFeet
import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryFootRim
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex







theorem exists_binary_exterior_ball_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K N A D : SimplicialComplex ℝ E)
    [Fintype K.faces] [Fintype N.faces] [Fintype D.faces]
    (hNK : N ≤ K) (hAN : A ≤ N) (hDN : D ≤ N)
    (hfullA : ∀ s ∈ N.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hfullD : ∀ s ∈ N.faces, (∀ v ∈ s, v ∈ D.vertices) → s ∈ D.faces)
    (hcard : ∀ s ∈ A.faces, s.card ≤ 2)
    {n : ℕ} (p : Fin (n + 2) → E) (hpi : Function.Injective p)
    (hverts : A.vertices = range p)
    (hedge : ∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces)
    (hcover : A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ))
    (hcontact : A.space ∩ D.space = {p 0, p (Fin.last (n + 1))})
    (hball :
      let T := fun i : Fin (n + 2) =>
        ((N.barycentricDualBlock {p i}).link (p i)).space ∪
          (D.barycentricDualBlock {p i}).space
      let J := fun i : Fin (n + 1) => (N.barycentricDualBlock {p i.castSucc, p i.succ}).space
      let Q := fun i : Fin (n + 1) =>
        ((N.barycentricDualBlock {p i.castSucc, p i.succ}).link
          (({p i.castSucc, p i.succ} : Finset E).centroid ℝ id)).space
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (N.barycentricNeighborhood A).space
        ((⋃ i, T i) \ ⋃ i, J i \ Q i)) :
    ∃ (h : E → ℝ) (F : E → E) (e : K.space ≃ₜ K.space),
      K.AffineOnFaces h ∧
      (∀ v ∈ K.vertices, (v ∈ A.vertices → h v = 1) ∧
        (v ∉ A.vertices → h v = 0)) ∧
      MapsTo h K.space (Icc (0 : ℝ) 1) ∧
      K.barycentricSubdivision.AffineOnFaces F ∧
      (∀ s : K.faces, F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices) ∧
      FinitePiecewiseAffineOn F K.space ∧ InjOn F K.space ∧
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧
      (∀ x : K.space, (e x : E) = F x) ∧
      (∀ L : SimplicialComplex ℝ E, L ≤ K → F '' L.space = L.space) ∧
      EqOn F id A.space ∧
      F '' (N.barycentricNeighborhood A).space =
        N.space ∩ {x | (1 / 2 : ℝ) ≤ h x} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (N.space ∩ {x | (1 / 2 : ℝ) ≤ h x})
        ((N.space ∩ {x | h x = (1 / 2 : ℝ)}) ∪
          (D.space ∩ {x | (1 / 2 : ℝ) ≤ h x})) ∧
      F '' (D.barycentricDualBlock {p 0}).space ∪
          F '' (D.barycentricDualBlock {p (Fin.last (n + 1))}).space =
        D.space ∩ {x | (1 / 2 : ℝ) ≤ h x} ∧
      ∀ z ∈ A.vertices, z ∈ D.vertices →
        F '' (((N.barycentricDualBlock {z}).link z).space ∩
          (D.barycentricDualBlock {z}).space) =
        (F '' (D.barycentricDualBlock {z}).space) ∩ {x | h x = (1 / 2 : ℝ)} := by
  classical
  obtain ⟨h, F, G, e, hh, hvalues, hbounds, hF, _, he, hei,
    hcenters, hval, _, hmarks, hfix, _, _⟩ :=
    K.exists_binaryNeighborhood_model A (hAN.trans hNK)
  have hhN : N.AffineOnFaces h := fun s hs => hh s (hNK hs)
  have hFN : N.barycentricSubdivision.AffineOnFaces F :=
    fun s hs => hF s (N.barycentricSubdivision_mono hNK hs)
  have hcentersN (s : N.faces) :
      F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices :=
    hcenters ⟨s.val, hNK s.property⟩
  have hvaluesN : ∀ v ∈ N.vertices, (v ∈ A.vertices → h v = 1) ∧
      (v ∉ A.vertices → h v = 0) := fun v hv => hvalues v (hNK hv)
  have hmarksN (L : SimplicialComplex ℝ E) (hLN : L ≤ N) :
      F '' L.space = L.space := (hmarks L (hLN.trans hNK)).1
  have hinj : InjOn F K.space := by
    intro x hx y hy hxy
    have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
      Subtype.ext ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.injective heq)
  have hFPL : FinitePiecewiseAffineOn F K.space := by
    simpa only [K.barycentricSubdivision_isSubdivision.space_eq] using
      hF.finitePiecewiseAffineOn K.barycentricSubdivision_finite
  have himage := N.image_barycentricNeighborhood_binaryCenters A hFN hcentersN hhN hvaluesN
  have hboundary := N.image_arc_chain_boundary_binaryLevel A D hAN hDN
    hfullA hfullD hcard p hpi hverts hedge hcover hcontact
    hFN hhN hcentersN hvaluesN hmarksN
  have hpne : p 0 ≠ p (Fin.last (n + 1)) := by
    intro hEq
    have h := congrArg Fin.val (hpi hEq)
    change 0 = n + 1 at h
    omega
  have hfeet := N.image_arc_feet_binaryLevel A D hAN hDN hfullA hpne hcontact
    hFN hcentersN hhN hvaluesN (hinj.mono (space_subset_of_le hNK)) (hmarksN D hDN)
  have hsub : (N.barycentricNeighborhood A).space ⊆ K.space := by
    intro x hx
    apply space_subset_of_le hNK
    exact N.barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le (N.barycentricNeighborhood_le A) hx)
  have htransport := hball.image_of_subset hFPL hsub hinj
  rw [himage, hboundary, hfeet] at htransport
  have hfinite : (A.space ∩ D.space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  refine ⟨h, F, e, hh, hvalues, hbounds, hF, hcenters, hFPL, hinj,
    he, hei, hval, fun L hLK => (hmarks L hLK).1, hfix, himage,
    htransport, hfeet, ?_⟩
  intro z hzA hzD
  exact N.image_endpoint_foot_rim_binaryLevel A D hDN hfullA hfinite
    hFN hhN hcentersN hvaluesN hmarksN hzA hzD

end Geometry.SimplicialComplex
