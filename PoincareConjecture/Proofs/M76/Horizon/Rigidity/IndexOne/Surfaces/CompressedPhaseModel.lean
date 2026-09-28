import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CompressedPhaseCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel












set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))



theorem exists_compressed_sourceSurface_finite_marked_model
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3)) (N : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3))
      (G : N ≃ₜ K.space) (g : (s → ℝ × V3) → N),
      IsCompact N ∧ R ⊆ interior N ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ z ∈ K.faces, (∀ w ∈ z, w ∈ (A i).vertices) → z ∈ (A i).faces) ∧
      K.space = F '' N ∧ (A 0).space = F '' R ∧
      (A 1).space = F '' frontier R ∧ (A 2).space = F '' sourceSurface phi theta ∧
      (A 3).space = F '' (sourceSurface phi theta ∩ frontier R) ∧
      (A 2).space ∩ (A 1).space = (A 3).space ∧
      (∀ x : N, (G x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (G.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (sourceSurface phi theta).Nonempty ∧
      ∀ x ∈ N, ∃ (i : α) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  let he := hphi.source_domain
  have hR := isCompact_latticeHandleDomain (Fin 1) (Fin 2) L
  have hS := sourceSurface_isCompact phi theta
  have hSne := sourceSurface_nonempty phi theta F0
  have hcharts := exists_compressed_sourceSurface_polyhedral_charts
    e phi heN hfront hAB hcorner
  let S := sourceSurface phi theta
  have hSR : S ⊆ R := sourceSurface_subset phi theta
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, F, N, K0, G0, hN, hRNint, _, hK0, hFc, hF, hG0, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e he.compatible he.cover hR isOpen_univ (subset_univ _)
  have hRN : R ⊆ N := hRNint.trans interior_subset
  have hFinj : InjOn F N := by
    intro x hx y hy hxy
    have h : G0 ⟨x, hx⟩ = G0 ⟨y, hy⟩ := Subtype.ext
      ((hG0 ⟨x, hx⟩).trans (hxy.trans (hG0 ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (G0.injective h)
  have hK0s : K0.space = F '' N := by
    ext z
    constructor
    · intro hz
      exact ⟨G0.symm ⟨z, hz⟩, (G0.symm ⟨z, hz⟩).property,
        (hG0 (G0.symm ⟨z, hz⟩)).symm.trans
          (congrArg Subtype.val (G0.apply_symm_apply ⟨z, hz⟩))⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hG0 ⟨x, hx⟩]
      exact (G0 ⟨x, hx⟩).property
  obtain ⟨P0, B0, _, hP0, _, hB0, hP0s, hB0s, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair
      e he.cover hFc hF hR (hFinj.mono hRN) he.halfspace
  obtain ⟨P, Q, hP, hQ, hPs, hQs0⟩ :=
    exists_compact_marked_polyhedral_image e he.cover hF hS
      (hFinj.mono (hSR.trans hRN)) hcharts
  have hQs : Q.space = F '' (S ∩ frontier R) := by
    simpa only [S, ← inter_assoc, inter_self] using hQs0
  let J : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3) := ![P0, B0, P, Q]
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    fin_cases i
    · exact hP0
    · exact hB0
    · exact hP
    · exact hQ
  have hJK : ∀ i, (J i).space ⊆ K0.space := by
    intro i
    rw [hK0s]
    fin_cases i
    · change P0.space ⊆ F '' N
      rw [hP0s]
      exact image_mono hRN
    · change B0.space ⊆ F '' N
      rw [hB0s]
      exact image_mono (he.closed.frontier_subset.trans hRN)
    · change P.space ⊆ F '' N
      rw [hPs]
      exact image_mono (hSR.trans hRN)
    · change Q.space ⊆ F '' N
      rw [hQs]
      exact image_mono (inter_subset_left.trans (hSR.trans hRN))
  obtain ⟨K, A, hK, hKK0, hA⟩ :=
    K0.exists_subdivision_with_finite_full_polyhedra hK0 J hJ hJK
  let G : N ≃ₜ K.space := G0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hGF (x : N) : (G x : s → ℝ × V3) = F x := hG0 x
  have hA0 : (A 0).space = F '' R := (hA 0).2.1.trans hP0s
  have hA1 : (A 1).space = F '' frontier R := (hA 1).2.1.trans hB0s
  have hA2 : (A 2).space = F '' S := (hA 2).2.1.trans hPs
  have hA3 : (A 3).space = F '' (S ∩ frontier R) := (hA 3).2.1.trans hQs
  have hAint : (A 2).space ∩ (A 1).space = (A 3).space := by
    rw [hA2, hA1, hA3]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, heq⟩⟩
      have hyx := hFinj (hRN (he.closed.frontier_subset hy)) (hRN (hSR hx)) heq
      exact ⟨x, ⟨hx, hyx ▸ hy⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  obtain ⟨x0, hx0⟩ := hSne
  let xN : N := ⟨x0, hRN (hSR hx0)⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K hK G F (Subset.refl N) xN hGF hproj
  refine ⟨s, F, N, K, A, G, g, hN, hRNint, hFc, hF, hK,
    ?_, hKK0.space_eq.trans hK0s, hA0, hA1, hA2, hA3, hAint,
    hGF, hgc, hg, hgPL, ⟨x0, hx0⟩, hproj⟩
  exact fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
