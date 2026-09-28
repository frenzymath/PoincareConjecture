import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart
import PoincareConjecture.Proofs.M76.Mathlib.RelativePolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePiecewiseAffineOn_real_rim_lift {L d u : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) (hu : u ∈ Ioo (-d) d)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {q : E → ℝ}
    (hq : ContinuousOn q K.space)
    (hf : FinitePiecewiseAffineOn
      (fun x ↦ annulusMap L hL ((q x : AddCircle (4 * L)), u)) K.space) :
    FinitePiecewiseAffineOn q K.space := by
  let : Fact (0 < 4 * L) := ⟨mul_pos (by norm_num) hL⟩
  obtain ⟨e, heS, heval, hePL⟩ := exists_annulus_PL_openPartialHomeomorph hL hd hwidth
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  let a := q x - 2 * L
  let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
    (OpenPartialHomeomorph.refl ℝ)
  let C := Q.trans e
  let r : K.space → ℝ × ℝ := fun y ↦ (q y, u)
  have hr : Continuous r := hq.domRestrict.prodMk continuous_const
  have hxC : r x ∈ C.source := by
    change ((q x ∈ Ioo a (a + 4 * L)) ∧ u ∈ univ) ∧ Q (q x, u) ∈ e.source
    refine ⟨⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
    · dsimp [a]; linarith
    · dsimp [a]; linarith
    · rw [heS]
      exact ⟨mem_univ _, hu⟩
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNW⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x (C.open_source.preimage hr) hxC
  have hNsource (y : E) (hy : y ∈ N.space) : (q y, u) ∈ C.source :=
    hNW (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)
  have hCv (y : E) : C (q y, u) = annulusMap L hL ((q y : AddCircle (4 * L)), u) := by
    change e (Q (q y, u)) = _
    rw [heval]
    rfl
  have hCPL : C ∈ piecewiseAffineGroupoid (ℝ × ℝ) := hePL a
  have hInv := ((mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) C).mp hCPL).2
  have hlocal := hInv.comp_finitePiecewiseAffineOn (hf.restrict N hN hNK) (by
    intro y hy
    dsimp only
    rw [← hCv]
    exact C.mapsTo (hNsource y hy))
  have hqN : FinitePiecewiseAffineOn q N.space :=
    (hlocal.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).congr (by
      intro y hy
      change (C.symm (annulusMap L hL ((q y : AddCircle (4 * L)), u))).1 = q y
      rw [← hCv, C.left_inv (hNsource y hy)])
  obtain ⟨J, hJ, hJs, hqJ⟩ := hqN
  exact ⟨J, W, hJ, hW, hxW, fun y hy ↦ hJs.symm.subset (hWN hy), hqJ⟩

end PoincareConjecture.M76.Dehn
