import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.SourceTorusBand



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.PeriodicSquare

variable {p : ℝ}

def squareSwap (p : ℝ) : Square p ≃ₜ Square p := Homeomorph.prodComm _ _

@[simp] theorem squareSwap_apply (z : Square p) : squareSwap p z = (z.2, z.1) := rfl

@[simp] theorem projection_squareSwap (z : Square p) :
    projection p (squareSwap p z) = (projection p z).swap := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} [Fact (0 < p)]


def SourceSquareMap.swap (M : SourceSquareMap p K) : SourceSquareMap p K where
  map := M.map.comp ⟨squareSwap p, (squareSwap p).continuous⟩
  surjective := M.surjective.comp (squareSwap p).surjective
  fibers z w := by
    change M.map (squareSwap p z) = M.map (squareSwap p w) ↔ _
    rw [M.fibers, ← projection_eq_iff, ← projection_eq_iff]
    simp only [projection_squareSwap, Prod.swap_inj]
  finite_piecewise_affine := by
    obtain ⟨F, hF, hvalue⟩ := M.finite_piecewise_affine
    obtain ⟨J, hJ, hJs, hfaces⟩ := hF
    have hF : FinitePiecewiseAffineOn F (squareCarrier p) := ⟨J, hJ, hJs, hfaces⟩
    let A := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap
    have hA : FinitePiecewiseAffineOn A (squareCarrier p) := by
      rw [← hJs]
      exact (J.affineOnFaces_affine A).finitePiecewiseAffineOn hJ
    have hmap : MapsTo A (squareCarrier p) (squareCarrier p) := by
      intro x hx
      exact ⟨hx.2, hx.1⟩
    refine ⟨F ∘ A, hF.comp hA hmap, ?_⟩
    intro z
    exact hvalue (squareSwap p z)

@[simp] theorem SourceSquareMap.swap_map (M : SourceSquareMap p K) (z : Square p) :
    M.swap.map z = M.map (squareSwap p z) := rfl



theorem SourceSquareMap.swap_homeomorph_value (M : SourceSquareMap p K)
    (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z) (z : Square p) :
    ((Homeomorph.prodComm _ _).trans h) (projection p z) = M.swap.map z :=
  hh (squareSwap p z)



theorem SourceSquareMap.swap_homeomorph_eq (M : SourceSquareMap p K)
    (h hs : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z)
    (hsvalue : ∀ z, hs (projection p z) = M.swap.map z) :
    hs = (Homeomorph.prodComm _ _).trans h := by
  apply Homeomorph.ext
  intro x
  obtain ⟨z, rfl⟩ := surjective_projection p x
  exact (hsvalue z).trans (M.swap_homeomorph_value h hh z).symm

theorem SourceSquareMap.swap_homeomorph_symm (M : SourceSquareMap p K)
    (h hs : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z)
    (hsvalue : ∀ z, hs (projection p z) = M.swap.map z) (x : K.space) :
    hs.symm x = (h.symm x).swap := by
  rw [M.swap_homeomorph_eq h hs hh hsvalue]
  rfl



theorem SourceSquareMap.exists_two_original_coordinate_bands
    [FiniteDimensional ℝ E]
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : ι → OpenPartialHomeomorph X V}
    (M : SourceSquareMap p K) {S : Set X} (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ S,
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      ∀ side : Bool,
      ∃ (b : C(AddCircle p × Icc (-r) r, S)) (f : (ℝ × ℝ) → X),
        IsEmbedding b ∧
        (∀ z, b z = h (if side then
          (((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p), z.1)
          else (z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p)))) ∧
        IsOpen (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) ∧
        PolyhedralPLInCharts e f (Icc (0 : ℝ) p ×ˢ Icc (-r) r) ∧
        (∀ s : Icc (0 : ℝ) p, ∀ t : Icc (-r) r,
          f ((s : ℝ), (t : ℝ)) = (b ((s : ℝ), t) : X)) ∧
        ∃ retract : C(S, AddCircle p), ∀ z, retract (b z) = z.1 := by
  obtain ⟨h, b, f, hvalue, hi, hb, hopen, hf, hfv, R, hR⟩ :=
    M.exists_original_coordinate_band H F hF hFval hr hwidth
  refine ⟨h, hvalue, ?_⟩
  intro side
  cases side
  · exact ⟨b, f, hi, hb, hopen, hf, hfv, R, hR⟩
  · obtain ⟨hs, bs, fs, hsvalue, his, hbs, hopens, hfs, hfsv, Rs, hRs⟩ :=
      M.swap.exists_original_coordinate_band H F hF hFval hr hwidth
    have heq : hs = (Homeomorph.prodComm _ _).trans h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      rw [hsvalue]
      exact (hvalue (squareSwap p z)).symm
    refine ⟨bs, fs, his, ?_, hopens, hfs, hfsv, Rs, hRs⟩
    intro z
    rw [hbs, heq]
    rfl

end PoincareConjecture.M76.PeriodicSquare
