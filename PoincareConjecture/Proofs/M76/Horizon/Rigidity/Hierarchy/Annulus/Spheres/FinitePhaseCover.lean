import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CompressedCircleModel









set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

theorem exists_finite_connected_cover_of_continuousOn_image
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X)
    (hg : ContinuousOn g K.space) :
    ∃ (n : ℕ) (T : Fin n → Set X), (⋃ i, T i) = g '' K.space ∧
      ∀ i, IsConnected (T i) := by
  classical
  let : Fintype K.faces := hK.fintype
  let index : Fin (Fintype.card K.faces) ≃ K.faces := (Fintype.equivFin K.faces).symm
  let T (i : Fin (Fintype.card K.faces)) := g '' convexHull ℝ ((index i).val : Set E)
  refine ⟨Fintype.card K.faces, T, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
      exact mem_image_of_mem g (K.convexHull_subset_space (index i).property hy)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
      refine mem_iUnion.mpr ⟨index.symm ⟨s, hs⟩, ?_⟩
      change g y ∈ g '' convexHull ℝ ((index (index.symm ⟨s, hs⟩)).val : Set E)
      rw [index.apply_symm_apply]
      exact mem_image_of_mem g hys
  · intro i
    apply IsConnected.image _ g (hg.mono (K.convexHull_subset_space (index i).property))
    apply (convex_convexHull ℝ _).isConnected
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (index i).property
    exact ⟨v, subset_convexHull ℝ _ hv⟩

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_compressed_phase_connected_cover
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other}))) :
    ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta} ∧
      ∀ i, IsConnected (T i) := by
  obtain ⟨s, F, K, B, g, _, _, _, hK, _, _, _, _, hg, _, _, hgs, _⟩ :=
    exists_hamiltonZero_compressed_circle_incidence e phi psi heR hA hAR hfixed hne hreg hN hfront
  obtain ⟨n, T, hT, hc⟩ := K.exists_finite_connected_cover_of_continuousOn_image hK g hg.continuousOn
  exact ⟨n, T, hT.trans hgs, hc⟩

theorem exists_hamiltonZero_compressed_paired_phase_connected_cover
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {a b : ℝ} (hne : (a : C0) ≠ (b : C0))
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0))
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)}))) :
    ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)}) ∧
      ∀ i, IsConnected (T i) := by
  obtain ⟨n, T, hT, hcT⟩ := exists_hamiltonZero_compressed_phase_connected_cover
    e phi psi heR hA hAR hfixed hne (hreg a (Or.inl rfl)) hN hfront
  obtain ⟨m, U, hU, hcU⟩ := exists_hamiltonZero_compressed_phase_connected_cover
    e phi psi heR hA hAR hfixed hne.symm (hreg b (Or.inr rfl)) hN
      (by simpa only [union_comm] using hfront)
  let index : Fin (n + m) ≃ Fin n ⊕ Fin m := finSumFinEquiv.symm
  let V : Fin (n + m) → Set X0 := fun i => Sum.elim T U (index i)
  refine ⟨n + m, V, ?_, ?_⟩
  · rw [← hT, ← hU]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases h : index i with
      | inl j => exact Or.inl (mem_iUnion.mpr ⟨j, by simpa [V, h] using hi⟩)
      | inr j => exact Or.inr (mem_iUnion.mpr ⟨j, by simpa [V, h] using hi⟩)
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨index.symm (Sum.inl i), by simpa [V] using hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨index.symm (Sum.inr i), by simpa [V] using hi⟩
  · intro i
    cases h : index i with
    | inl j => simpa [V, h] using hcT j
    | inr j => simpa [V, h] using hcU j

end PoincareConjecture.M76
