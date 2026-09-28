import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.BallBoundaryPolygons
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallDiskPush

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_ball_polygon_contact_disk
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] [Nonempty ι]
    {B R : Set E} (hB : IsFinitePLBallPair V3 B R)
    (M : SimplicialComplex ℝ E) (hM : M.faces.Finite) (hMB : M.space ⊆ B)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hsub : ∀ i, (P i).boundary ℝ ⊆ R)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (hboundary : R ∩ M.space = ⋃ i, (P i).boundary ℝ) :
    ∃ i d, IsFinitePLBallPair (ℝ × ℝ) d ((P i).boundary ℝ) ∧
      d ⊆ B ∧ d ∩ R = (P i).boundary ℝ ∧ d ∩ M.space = (P i).boundary ℝ := by
  obtain ⟨i,d,hd,hdR,hdP⟩ := hB.exists_innermost_boundary_polygon_disk n P hP hi hsub hdis
  have hcontact : d ∩ M.space = (P i).boundary ℝ := by
    rw [←hdP,←hboundary]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,hdR hx.1,hx.2⟩
    · intro hx
      exact ⟨hx.1,hx.2.2⟩
  obtain ⟨k,_,_,hkB,_,hkd,hkM,hkR⟩ :=
    exists_finitePL_boundary_disk_push_avoiding_complex hB hd hdR M hM hMB hcontact
  exact ⟨i,k '' d,hkd,hkB.image_subset,hkR,hkM⟩

end PoincareConjecture.M76
