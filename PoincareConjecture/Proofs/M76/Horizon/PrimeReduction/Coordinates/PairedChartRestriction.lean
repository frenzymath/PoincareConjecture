import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.CoordinateTriangleEndpointCrossing

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_ordered_interior_crossing_chart
    (B : OpenPartialHomeomorph V3 C3)
    (hB : LocallyPiecewiseAffineOn B B.source)
    (hBi : LocallyPiecewiseAffineOn B.symm B.target)
    {p : V3} (hp : p ∈ B.source) (hBp : B p = 0)
    (D : Fin 2 → Set V3)
    (hD0 : ∀ x ∈ B.source, x ∈ D 0 ↔ (B x).1.1 = 0)
    (hD1 : ∀ x ∈ B.source, x ∈ D 1 ↔ (B x).2 = 0) :
    ∃ H : OpenPartialHomeomorph V3 V3,
      H ∈ piecewiseAffineGroupoid V3 ∧ p ∈ H.source ∧
      H.source = B.source ∧ H p = 0 ∧
      ∀ i x, x ∈ H.source → (x ∈ D i ↔ H x i.castSucc = 0) := by
  let E := crossingCoordinateOrder
  let H := B.trans E.toHomeomorph.toOpenPartialHomeomorph
  have hH : H ∈ piecewiseAffineGroupoid V3 := by
    exact ⟨(locallyPiecewiseAffineOn_affine E.toContinuousAffineMap isOpen_univ).comp hB,
      hBi.comp (locallyPiecewiseAffineOn_affine E.symm.toContinuousAffineMap isOpen_univ)⟩
  have hs : H.source = B.source := by
    change B.source ∩ B ⁻¹' univ = B.source
    simp
  refine ⟨H, hH, hs.symm.subset hp, hs, ?_, ?_⟩
  · change E (B p) = 0
    rw [hBp]
    ext i
    fin_cases i <;> rfl
  · intro i x hx
    fin_cases i
    · exact hD0 x (hs.subset hx)
    · exact hD1 x (hs.subset hx)

theorem exists_disjoint_endpoint_axis_charts
    (A : Set V3) (D : Fin 2 → Set V3) (p : Fin 2 → V3)
    (hne : p 0 ≠ p 1)
    (W : Set V3) (hW : IsOpen W)
    (hpW : ∀ i, p i ∈ W)
    (hisolate : ∀ x ∈ W, x ∈ A ↔ x ∈ D 0 ∧ x ∈ D 1)
    (B : Fin 2 → OpenPartialHomeomorph V3 V3)
    (hB : ∀ i, B i ∈ piecewiseAffineGroupoid V3)
    (hpB : ∀ i, p i ∈ (B i).source) (hBp : ∀ i, B i (p i) = 0)
    (htriangle : ∀ i x, x ∈ (B i).source →
      (x ∈ D 0 ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2))
    (hsphere : ∀ i x, x ∈ (B i).source → (x ∈ D 1 ↔ B i x 1 = 0)) :
    ∃ H : Fin 2 → OpenPartialHomeomorph V3 V3,
      (∀ i, H i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (H i).source ∧
        (H i).source ⊆ W ∧ H i (p i) = 0) ∧
      Pairwise (fun i j => Disjoint (H i).source (H j).source) ∧
      (∀ i x, x ∈ (H i).source →
        (x ∈ A ↔ H i x 0 = 0 ∧ H i x 1 = 0 ∧ 0 ≤ H i x 2)) ∧
      (∀ i x, x ∈ (H i).source →
        (x ∈ D 0 ↔ H i x 0 = 0 ∧ 0 ≤ H i x 2)) ∧
      ∀ i x, x ∈ (H i).source → (x ∈ D 1 ↔ H i x 1 = 0) := by
  classical
  obtain ⟨U0, U1, hU0, hU1, hp0, hp1, hdis⟩ := t2_separation hne
  let U : Fin 2 → Set V3 := ![U0, U1]
  have hU (i : Fin 2) : IsOpen (U i) := by fin_cases i <;> assumption
  have hpU (i : Fin 2) : p i ∈ U i := by fin_cases i <;> assumption
  let H (i : Fin 2) := (B i).restrOpen (W ∩ U i) (hW.inter (hU i))
  have hsource (i : Fin 2) : (H i).source ⊆ W := fun _ hx => hx.2.1
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨⟨(hB i).1.mono (H i).open_source inter_subset_left,
      (hB i).2.mono (H i).open_target inter_subset_left⟩,
      ⟨hpB i, hpW i, hpU i⟩, hsource i, hBp i⟩
  · intro i j hij
    have hUi : (H i).source ⊆ U i := fun _ hx => hx.2.2
    have hUj : (H j).source ⊆ U j := fun _ hx => hx.2.2
    apply Disjoint.mono hUi hUj
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  · intro i x hx
    rw [hisolate x (hsource i hx), htriangle i x hx.1, hsphere i x hx.1]
    tauto
  · exact fun i x hx => htriangle i x hx.1
  · exact fun i x hx => hsphere i x hx.1

end PoincareConjecture.M76
