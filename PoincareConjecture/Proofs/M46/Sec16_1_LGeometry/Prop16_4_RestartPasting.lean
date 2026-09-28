import PoincareConjecture.Proofs.M14.Sec6_3_InitialValueContinuation









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}





theorem exists_initialValuePath_of_matching_restart
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T l r d : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hrd : r < d)
    {x y z₀ z₁ : G.Point} {Z : G.Horizontal x}
    (P : M14SquareRootInitialValuePath G T (r ^ 2) x y Z)
    {p : M14BackwardPath G T (l ^ 2) (d ^ 2) z₀ z₁}
    (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve
      (M14SqrtParameterInterval (l ^ 2) (d ^ 2)) R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval (l ^ 2) (d ^ 2), ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    (hpoint : R.curve r = P.square_path.curve r)
    (hvel : HEq (R.horizontal_velocity r) (P.square_path.horizontal_velocity r)) :
    ∃ z : G.Point, ∃ Q : M14SquareRootInitialValuePath G T (d ^ 2) x z Z,
      EqOn Q.square_path.curve P.square_path.curve (Icc 0 r) := by
  have hr : 0 < r := hl.trans_lt hlr
  have hd : 0 < d := hr.trans hrd
  have hCP : M14SqrtParameterInterval 0 (r ^ 2) = Icc 0 r := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hr.le]
  have hCR : M14SqrtParameterInterval (l ^ 2) (d ^ 2) = Icc l d := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl, Real.sqrt_sq hd.le]
  have hsubP : Icc l r ⊆ M14SqrtParameterInterval 0 (r ^ 2) := by
    rw [hCP]
    exact Icc_subset_Icc hl le_rfl
  have hsubR : Icc l r ⊆ M14SqrtParameterInterval (l ^ 2) (d ^ 2) := by
    rw [hCR]
    exact Icc_subset_Icc le_rfl hrd.le
  have heq : EqOn P.square_path.curve R.curve (Icc l r) := by
    have hh := M14.squareRootEuler_unique hM04 hM12 R P.square_path hlr hsubR hsubP
      E P.extension (fun s hs => hEuler s (hsubR hs))
      (fun s hs => P.euler s (hsubP hs)) ⟨hlr.le, le_rfl⟩ hpoint hvel
    exact fun s hs => (hh s hs).1.symm
  let c := (l + r) / 2
  have hlc : l < c := by dsimp only [c]; linarith
  have hcr : c < r := by dsimp only [c]; linarith
  have hc : 0 < c := hl.trans_lt hlc
  have hcrSq : c ^ 2 < r ^ 2 := (sq_lt_sq₀ hc.le hr.le).mpr hcr
  let P₀ := M14.initialValuePathRestrict P (sq_pos_of_pos hc) hcrSq.le
  have hoverlap : EqOn P₀.square_path.curve R.curve
      (M14SqrtParameterInterval (l ^ 2) (c ^ 2)) := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl, Real.sqrt_sq hc.le]
    exact fun s hs => heq ⟨hs.1, hs.2.trans hcr.le⟩
  obtain ⟨z, Q, _, _⟩ := M14.exists_initialValuePath_of_overlap hM12 P₀ R E hEuler
    ((sq_lt_sq₀ hl hc.le).mpr hlc) ((sq_lt_sq₀ hc.le hd.le).mpr (hcr.trans hrd))
    hoverlap
  have hsame := M14.initialValuePath_square_eqOn hM04 hM12 Q P
  rw [min_eq_right ((sq_le_sq₀ hr.le hd.le).mpr hrd.le), hCP] at hsame
  exact ⟨z, Q, hsame⟩

end PoincareConjecture.Proofs.M46
