import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Original.AnnularCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.AnnularExtension
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition



set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

local notation "Ann" => squareAnnulus 8 1

theorem originalAnnularExtension_conjugacy
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D C : Set E} {S B : Set X}
    (H : D ≃ₜ S) (A : Ann ≃ₜ B) (q : Ann ≃ₜ C)
    (hCD : C ⊆ D) (hBS : B ⊆ S) (hC : IsClosed C) (hB : IsClosed B)
    (hvalue : ∀ z : Ann, (H ⟨q z, hCD (q z).property⟩ : X) = (A z : X))
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x) (x : D) :
    H (originalAnnularExtension q hCD hC
      (isOpen_original_annular_coordinate_mark H A q hCD hvalue hopen) G hfix x) =
      originalAnnularExtension A hBS hB hopen G hfix (H x) := by
  let hopenq := isOpen_original_annular_coordinate_mark H A q hCD hvalue hopen
  by_cases hx : (x : E) ∈ C
  · let z := q.symm ⟨x, hx⟩
    have hxz : (⟨q z, hCD (q z).property⟩ : D) = x := by
      apply Subtype.ext
      exact congrArg (fun y : C => (y : E)) (q.apply_symm_apply ⟨x, hx⟩)
    have hHz (z : Ann) : H ⟨q z, hCD (q z).property⟩ =
        ⟨A z, hBS (A z).property⟩ := Subtype.ext (hvalue z)
    rw [← hxz, originalAnnularExtension_apply, hHz (G z), hHz z,
      originalAnnularExtension_apply]
  · have hn : (x : E) ∉ originalAnnulusOpenMark q :=
      fun hm => hx (originalAnnulusOpenMark_subset q hm)
    rw [originalAnnularExtension_fixed_off_mark q hCD hC hopenq G hfix x hn,
      originalAnnularExtension_fixed_off_mark A hBS hB hopen G hfix (H x)
        (fun hm => hn ((original_annular_coordinate_mark_iff H A q hCD hvalue x).mpr hm))]

theorem exists_originalAnnularExtension_originalPL
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {S B : Set X}
    (H : K.space ≃ₜ S) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X))
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X))
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x) :
    ∃ g : E → X, PolyhedralPLInCharts e g K.space ∧
      ∀ x : K.space, g x = (originalAnnularExtension A hBS hB hopen G hfix (H x) : X) := by
  obtain ⟨C, hCK, q, _, hC, hq, _, _, hqval, _⟩ :=
    exists_finitePL_original_annular_coordinates e hcompat H F hF hFval A hBS j hj hjval
  let hopenq := isOpen_original_annular_coordinate_mark H A q hCK hqval hopen
  let D := originalAnnularExtension q hCK hC hopenq G hfix
  obtain ⟨f, hf, hfv⟩ := isFinitePL_originalAnnularExtension K hK q hq hCK hC hopenq G hG hfix
  have hmaps : MapsTo f K.space K.space := by
    intro x hx
    rw [← hfv ⟨x, hx⟩]
    exact (D ⟨x, hx⟩).property
  refine ⟨F ∘ f, hF.comp_finitePiecewiseAffineOn K hK hf hmaps, ?_⟩
  intro x
  change F (f x) = _
  rw [← hfv x, hFval]
  exact congrArg Subtype.val
    (originalAnnularExtension_conjugacy H A q hCK hBS hC hB hqval hopen G hfix x)

end PoincareConjecture.M76.Dehn
