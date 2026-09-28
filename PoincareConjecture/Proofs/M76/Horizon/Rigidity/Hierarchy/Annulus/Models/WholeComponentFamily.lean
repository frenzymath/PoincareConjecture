import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CompressedCircleModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.ModelComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.TerminalAnnuli

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in
theorem exists_hamiltonZero_compressed_whole_component_family
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
    let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}
    ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = S ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
        ∀ x ∈ T i, connectedComponentIn S x = T i := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}
  obtain ⟨s, F, K, _, g, hFc, hFi, _, hK, _, _, hKs, _,
    hgPL, hgi, hFg, hgS, _⟩ :=
    exists_hamiltonZero_compressed_circle_incidence e phi psi heR hA hAR hfixed hne hreg hN hfront
  let : DecidableEq (s → ℝ × V3) := Classical.decEq _
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let I := K.vertexAbstractComplex.edgeGraph.ConnectedComponent
  let : Fintype I := Fintype.ofFinite I
  let U (i : I) := g '' (K.edgeComponentComplex i).space
  have hsub (i : I) : (K.edgeComponentComplex i).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le i)
  have hUS (i : I) : U i ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgS.subset ⟨z, hsub i hz, rfl⟩
  have hUK (i : I) : IsCompact (U i) :=
    ((K.edgeComponentComplex i).isCompact_space_of_finite
      (hK.subset (K.edgeComponentComplex_le i))).image_of_continuousOn
        (hgPL.continuousOn.mono (hsub i))
  have hUconn (i : I) : IsPathConnected (U i) :=
    (K.edgeComponentComplex_isPathConnected i).image' (hgPL.continuousOn.mono (hsub i))
  have hUcover : (⋃ i, U i) = S := by
    change (⋃ i, g '' (K.edgeComponentComplex i).space) = _
    rw [← image_iUnion, K.iUnion_edgeComponentComplex_space]
    exact hgS
  have hUdis : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have heq := hgi (hsub j hw) (hsub i hz) hwz
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hij) hz (heq ▸ hw)
  have hFK (y : X0) (hy : y ∈ S) : F y ∈ K.space := hKs.symm.subset ⟨y, hy, rfl⟩
  have hgF (y : X0) (hy : y ∈ S) : g (F y) = y := hFi (hFg (F y) (hFK y hy))
  have hcomponent (i : I) (x : X0) (hx : x ∈ U i) : connectedComponentIn S x = U i := by
    apply Subset.antisymm
    · have hxS := hUS i hx
      have hxP : F x ∈ (K.edgeComponentComplex i).space := by
        obtain ⟨z, hz, rfl⟩ := hx
        rw [hFg z (hsub i hz)]
        exact hz
      have hm := hFc.continuousOn.image_connectedComponentIn_subset hxS
      rw [← hKs, HamiltonIntervalTorus.edgeComponentComplex_connectedComponentIn K hK i hxP] at hm
      intro y hy
      exact ⟨F y, hm ⟨y, hy, rfl⟩, hgF y (connectedComponentIn_subset S x hy)⟩
    · exact (hUconn i).isConnected.isPreconnected.subset_connectedComponentIn hx (hUS i)
  let r := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => U (r.symm i), ?_, ?_, ?_⟩
  · calc
      (⋃ i, U (r.symm i)) = ⋃ i, U i := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨r.symm i, hi⟩
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨r i, by simpa using hi⟩
      _ = S := hUcover
  · intro i j hij
    exact hUdis (fun h => hij (r.symm.injective h))
  · intro i
    exact ⟨hUK (r.symm i), hUconn (r.symm i), hcomponent (r.symm i)⟩

theorem exists_hamiltonZero_terminal_finite_annulus_family
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi0 psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi0 x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi0 (theta : C0))
    (geometry : HamiltonZeroSecondPhaseGeometry e R psi a b)
    (hcover : ∀ theta ∈ ({a, b} : Set ℝ),
      IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi0 (frontier R) theta))
    (hterminal : ∀ theta ∈ ({a, b} : Set ℝ), ∀ T : Set X0, T.Nonempty →
      T ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)} →
      (∀ x ∈ T, connectedComponentIn
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x = T) →
      (T ∩ frontier R).Nonempty) :
    ∀ theta ∈ ({a, b} : Set ℝ),
      let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
      ∃ (n : ℕ) (T : Fin n → Set X0),
        (⋃ i, T i) = S ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
        ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
          (∀ x ∈ T i, connectedComponentIn S x = T i) ∧
          ∃ H : squareAnnulus 8 1 ≃ₜ T i, ∃ f : (ℝ × ℝ) → X0,
            PolyhedralPLInCharts e f (squareAnnulus 8 1) ∧
            (∀ z : squareAnnulus 8 1, f z = (H z : X0)) ∧
            ∀ z : squareAnnulus 8 1,
              depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
                (H z : X0) ∈ frontier R := by
  have hne : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp h)
  have hannuli := exists_hamiltonZero_terminal_component_annuli e phi0 psi heR hA hAR hfixed
    ha hab hb hreg geometry hcover hterminal
  intro theta htheta S
  have hfamily : ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = S ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
        ∀ x ∈ T i, connectedComponentIn S x = T i := by
    rcases htheta with rfl | rfl
    · exact exists_hamiltonZero_compressed_whole_component_family e phi0 psi heR hA hAR hfixed
        hne (hreg _ (Or.inl rfl)) (geometry.slabs false).1 (geometry.slabs false).2.1
    · exact exists_hamiltonZero_compressed_whole_component_family e phi0 psi heR hA hAR hfixed
        hne.symm (hreg _ (Or.inr rfl)) (geometry.slabs false).1
        (by simpa only [union_comm] using (geometry.slabs false).2.1)
  obtain ⟨n, T, hT, hdis, hprops⟩ := hfamily
  refine ⟨n, T, hT, hdis, ?_⟩
  intro i
  have hiS : T i ⊆ S := by rw [← hT]; exact subset_iUnion T i
  exact ⟨(hprops i).1, (hprops i).2.1, (hprops i).2.2,
    hannuli theta htheta (T i) (hprops i).2.1.nonempty hiS (hprops i).2.2⟩

end PoincareConjecture.M76
