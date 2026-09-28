import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FinitePLBallInteriorChart









set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SeparatedSphereCaps

variable {X ι : Type*}



theorem cap_interior_preimage_eq_compl (P : Set X) (D : ι → Set X) (i : ι)
    {B : Set X} (hattach : D i ∩ P = B)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    (Subtype.val : (P ∪ ⋃ j, D j : Set X) → X) ⁻¹' (D i \ B) =
      ((Subtype.val : (P ∪ ⋃ j, D j : Set X) → X) ⁻¹'
        (P ∪ ⋃ j : {j // j ≠ i}, D j))ᶜ := by
  classical
  ext x
  constructor
  · rintro ⟨hxD, hxB⟩ (hxP | hxOther)
    · exact hxB (hattach.subset ⟨hxD, hxP⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hxOther
      exact disjoint_left.mp (hdis j.property.symm) hxD hj
  · intro hx
    have hxP : (x : X) ∉ P := fun h => hx (Or.inl h)
    have hxD : (x : X) ∈ D i := by
      obtain ⟨j, hj⟩ := mem_iUnion.mp (x.property.resolve_left hxP)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact False.elim (hx (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)))
    exact ⟨hxD, fun hB => hxP (hattach.symm.subset hB).2⟩



theorem isOpen_cap_interior [TopologicalSpace X] [Finite ι] (P : Set X) (D : ι → Set X)
    (hP : IsClosed P) (hD : ∀ i, IsClosed (D i)) (i : ι)
    {B : Set X} (hattach : D i ∩ P = B)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    IsOpen ((Subtype.val : (P ∪ ⋃ j, D j : Set X) → X) ⁻¹' (D i \ B)) := by
  rw [cap_interior_preimage_eq_compl P D i hattach hdis]
  exact ((hP.union (isClosed_iUnion_of_finite (fun j : {j // j ≠ i} => hD j))).preimage
    continuous_subtype_val).isOpen_compl

end Geometry.SeparatedSphereCaps

namespace Set

local notation "V3" => (Fin 3 → ℝ)

variable {E W ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite ι]



theorem IsFinitePLBallPair.exists_finite_cap_interior_chart
    (P : Set E) (D : ι → Set E) (hP : IsClosed P)
    (hclosed : ∀ i, IsClosed (D i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (i : ι)
    {B : Set E} (hD : IsFinitePLBallPair W (D i) B) (hattach : D i ∩ P = B)
    (c : W ≃L[ℝ] V3) {p : E} (hp : p ∈ D i \ B) :
    ∃ (e : OpenPartialHomeomorph (P ∪ ⋃ j, D j : Set E) V3)
      (f : E → V3) (g : V3 → E),
      e.source = (Subtype.val : (P ∪ ⋃ j, D j : Set E) → E) ⁻¹' (D i \ B) ∧
      e.target = interior (closedBall (0 : V3) 1) ∧
      (⟨p, Or.inr (mem_iUnion.mpr ⟨i, hp.1⟩)⟩ : (P ∪ ⋃ j, D j : Set E)) ∈ e.source ∧
      FinitePiecewiseAffineOn f (D i) ∧
      FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
      (∀ x : (P ∪ ⋃ j, D j : Set E), e x = f x) ∧
      (∀ y ∈ closedBall (0 : V3) 1, (e.symm y : E) = g y) ∧
      MapsTo g (closedBall (0 : V3) 1) (D i) ∧
      LeftInvOn g f (D i) ∧ RightInvOn g f (closedBall (0 : V3) 1) := by
  have hDT : D i ⊆ P ∪ ⋃ j, D j :=
    fun _ hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  obtain ⟨e, f, g, hs, ht, hf, hg, hef, heg, hgm, hgf, hfg⟩ :=
    hD.exists_open_cube_interior_chart c hDT
      (Geometry.SeparatedSphereCaps.isOpen_cap_interior P D hP hclosed i hattach hdis)
  exact ⟨e, f, g, hs, ht, hs.symm ▸ hp, hf, hg, hef, heg, hgm, hgf, hfg⟩

end Set
