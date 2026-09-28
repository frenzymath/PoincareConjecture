import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid




set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_compatible_chart_restriction
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E) (T : OpenPartialHomeomorph X E)
    (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E)
    {U : Set X} (hU : IsOpen U) :
    ∃ G : OpenPartialHomeomorph X E,
      G.source = T.source ∩ U ∧ (∀ x, G x = T x) ∧
      ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E := by
  let W := T.target ∩ T.symm ⁻¹' U
  have hW : IsOpen W :=
    T.symm.continuousOn.isOpen_inter_preimage T.open_target hU
  let I := OpenPartialHomeomorph.ofSet W hW
  let G := T.trans I
  have hI : I ∈ piecewiseAffineGroupoid E :=
    ⟨locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW,
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW⟩
  refine ⟨G, ?_, fun _ => rfl, ?_⟩
  · ext x
    change (x ∈ T.source ∧ T x ∈ T.target ∧ T.symm (T x) ∈ U) ↔
      x ∈ T.source ∧ x ∈ U
    constructor
    · rintro ⟨hx, _, hxu⟩
      exact ⟨hx, by simpa only [T.left_inv hx] using hxu⟩
    · rintro ⟨hx, hxu⟩
      exact ⟨hx, T.mapsTo hx, by simpa only [T.left_inv hx] using hxu⟩
  · intro i
    simpa only [G, OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans (hT i) hI

end PoincareConjecture.M76.HamiltonIntervalTorus
