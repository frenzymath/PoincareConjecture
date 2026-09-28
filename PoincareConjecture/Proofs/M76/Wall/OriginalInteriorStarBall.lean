import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.OriginalDiskStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem isFinitePLBallPair_original_interior_star
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (hpR : (g p : X) ∈ interior R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z))) :
    IsFinitePLBallPair V3 (K.closedStar p).space ((K.closedStar p).link p).space := by
  classical
  obtain ⟨hinj, _, hint⟩ :=
    K.exists_original_open_neighborhood_inside_closedStar hK H g hg hp hpR B hsource
  let N := K.closedStar p
  let f : E → V3 := fun z => B (g z)
  have hN : N.faces.Finite := finite_closedStar_faces hK p
  have hpN : p ∈ N.vertices := by
    change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
    exact ⟨hp, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      using (show {p} ∈ K.faces from hp)⟩
  have hself : N.closedStar p = N := by
    ext s
    change ((s ∈ K.faces ∧ insert p s ∈ K.faces) ∧
      insert p s ∈ K.faces ∧ insert p (insert p s) ∈ K.faces) ↔
      s ∈ K.faces ∧ insert p s ∈ K.faces
    simp only [Finset.insert_idem]
    tauto
  let J := hface.embeddedImage hinj
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj hN
  have hpJ : f p ∈ J.vertices := by
    rw [hface.embeddedImage_vertices hinj]
    exact ⟨p, hpN, rfl⟩
  have hJint : f p ∈ interior J.space := by
    rw [hface.embeddedImage_space hinj]
    exact hint
  have hJstar : (J.closedStar (f p)).space = f '' N.space := by
    rw [hface.embeddedImage_closedStar_space hinj hpN, hself]
  have hJlink : (J.link (f p)).space = f '' (N.link p).space :=
    hface.embeddedImage_link_space hinj hpN
  have hball := J.isFinitePLBallPair_closedStar_of_interior hJ hpJ hJint
    (ContinuousLinearEquiv.refl ℝ V3)
  rw [hJstar, hJlink] at hball
  obtain ⟨A, hA, hAval⟩ := (hface.finitePiecewiseAffineOn hN).exists_homeomorph_image hinj
  have hlink : (N.link p).space ⊆ N.space :=
    space_subset_of_le (show N.link p ≤ N from fun _ hs => hs.1)
  apply hball.of_homeomorph hlink A hA
  intro x
  rw [hAval]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    have hyx : y = x := hinj (hlink hy) x.property heq
    exact hyx ▸ hy

end PoincareConjecture.M76
