import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.TwoCapTriangulation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.StandardCircleOrder
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.SquareRimEulerCount
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FinitePLImageFaceBounds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PLSurfaceCount
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1


theorem circle_surfaceEulerCount (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (gamma : Q2 ≃ₜ K.space) (hgamma : gamma.IsFinitePL) :
    K.surfaceEulerCount = 0 := by
  obtain ⟨Square, hSquare, hSquares⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨g, hg, hgv⟩ := hgamma
  have hf : FinitePiecewiseAffineOn g Square.space := hSquares.symm ▸ hg
  have hinj : InjOn g Square.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (gamma.injective (Subtype.ext
      ((hgv ⟨x, hSquares.subset hx⟩).trans
        (hxy.trans (hgv ⟨y, hSquares.subset hy⟩).symm))))
  have himage : g '' Square.space = K.space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hgv ⟨x, hSquares.subset hx⟩) ▸ (gamma ⟨x, hSquares.subset hx⟩).property
    · intro hy
      let x := gamma.symm ⟨y, hy⟩
      exact ⟨x, hSquares.symm.subset x.property, (hgv x).symm.trans
        (congrArg Subtype.val (gamma.apply_symm_apply ⟨y, hy⟩))⟩
  have hdim : ∀ s ∈ Square.faces, s.card ≤ 3 := by
    intro s hs
    have h := (Square.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa using h
  have htarget := hf.face_card_le_of_image hSquare hdim K himage.symm.subset
  exact (hf.surfaceEulerCount_eq_of_injOn hSquare hK hdim htarget hinj himage).symm.trans
    (CompressionCylinder.square_rim_surfaceEulerCount Square hSquare hSquares)

open Classical in


theorem exists_two_circle_cap_triangulation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdimK : ∀ s ∈ K.faces, s.card ≤ 3)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ b, L b ≤ K)
    (gamma : ∀ b, Q2 ≃ₜ (L b).space) (hgamma : ∀ b, (gamma b).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧
      J.space = ((fun x : E ↦ (x, (0 : ℝ))) '' K.space ∪
        boundaryCircleCap false (L false).space) ∪ boundaryCircleCap true (L true).space ∧
      (∀ s ∈ J.faces, s.card ≤ 3) ∧
      J.surfaceEulerCount = K.surfaceEulerCount + 2 ∧
      ∀ s ∈ K.faces, s.image (fun x : E ↦ (x, (0 : ℝ))) ∈ J.faces := by
  classical
  have hL (b : Bool) : (L b).faces.Finite := hK.subset (hLK b)
  have hne (b : Bool) : (L b).space.Nonempty :=
    ⟨_, (gamma b ⟨fun _ ↦ 1, by simp⟩).property⟩
  have hdimL (b : Bool) : ∀ s ∈ (L b).faces, s.card ≤ 2 :=
    (exists_original_boundary_circle_order (gamma b) (hgamma b) (L b) (hL b) rfl).1
  obtain ⟨J, hJ, hJs, hdimJ, hcount, hfaces⟩ :=
    exists_two_cap_triangulation K hK hdimK L hLK hne hdimL hdis
  refine ⟨J, hJ, hJs, hdimJ, ?_, hfaces⟩
  simpa only [circle_surfaceEulerCount (L false) (hL false) (gamma false) (hgamma false),
    circle_surfaceEulerCount (L true) (hL true) (gamma true) (hgamma true), sub_zero]
    using hcount

end PoincareConjecture.M76.Dehn.Annuli
