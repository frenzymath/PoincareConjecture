import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SecondCoordinateSurface
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.FiniteTerminalPair
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedraSubcomplexes
import PoincareLib.Topology.Manifold.Smoothing.RelativeApproximation.General.ModelInverse
import PoincareLib.Topology.Manifold.Smoothing.RelativeApproximation.General.InteriorSourceModel

/-!
# A finite marked model of the retained cut and second source surface

One original-atlas graph model retains the cut, its complete old frontier,
the selected second-coordinate surface, and its entire rim as full finite
subcomplexes. The ambient carrier supplies the total inverse without a
nonemptiness assumption on the surface. See Hudson 1969, pp. 12--19, and
Waldhausen 1968, pp. 59--60.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

/-- The actual original map and retained PL domain construct one finite
model with the whole old frontier and whole second-surface rim marked.
The same selected phase retains compactness and all its regular charts.
No connectedness, annulus type, or rim-component count is assumed. -/
theorem exists_hamiltonZero_second_surface_finite_marked_model {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ t ∈ Ioo (0 : ℝ) p,
      let S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(t : C0)}
      IsCompact S ∧ HamiltonZeroSecondCoordinateRegularity e R phi (t : C0) ∧
      ∃ (s : Finset (univ : Set X0)) (F : X0 → (s → ℝ × V3)) (N : Set X0)
        (K : SimplicialComplex ℝ (s → ℝ × V3))
        (A : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3))
        (G : N ≃ₜ K.space) (g : (s → ℝ × V3) → N),
        IsCompact N ∧ N = univ ∧ Continuous F ∧
        (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
        K.faces.Finite ∧
        (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
          ∀ z ∈ K.faces, (∀ v ∈ z, v ∈ (A i).vertices) → z ∈ (A i).faces) ∧
        K.space = F '' N ∧ (A 0).space = F '' R ∧
        (A 1).space = F '' frontier R ∧ (A 2).space = F '' S ∧
        (A 3).space = F '' (S ∩ frontier R) ∧
        (A 2).space ∩ (A 1).space = (A 3).space ∧
        (∀ x : N, (G x : s → ℝ × V3) = F x) ∧
        ContinuousOn g K.space ∧
        (∀ z : K.space, (g z : X0) = (G.symm z : X0)) ∧
        PolyhedralPLInCharts e (fun z => (g z : X0)) K.space ∧
        ∀ x ∈ N, ∃ (i : ι) (V : Set X0) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  obtain ⟨t, ht, hS, hregular, hcharts⟩ :=
    exists_hamiltonZero_second_surface_polyhedral_charts e d hd phi hphi he
  let S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(t : C0)}
  have hSR : S ⊆ R := inter_subset_left
  have hR : IsCompact R :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset he.closed (subset_univ _)
  let : T2Space (V3 ⧸ hamiltonZeroPeriodLattice.toAddSubgroup) :=
    hamiltonZeroLatticeProductEquiv.isEmbedding.t2Space
  let : LocallyCompactSpace X0 := he.locallyCompactSpace
  obtain ⟨s, F, N, K0, G0, hN, hXNint, _, hK0, hFc, hF, hG0, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e he.compatible he.cover isCompact_hamiltonZeroAmbient isOpen_univ (subset_univ _)
  have hXN : (univ : Set X0) ⊆ N := hXNint.trans interior_subset
  have hNuniv : N = univ := Set.Subset.antisymm (subset_univ _) hXN
  have hRN : R ⊆ N := (subset_univ _).trans hXN
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
  obtain ⟨P, Q, hP, hQ, hPs, hQs⟩ :=
    HamiltonIntervalTorus.exists_compact_marked_polyhedral_image e he.cover hF hS
      (hFinj.mono (hSR.trans hRN)) hcharts
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
  let xN : N := ⟨0, hXN (mem_univ _)⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K hK G F (Subset.refl N) xN hGF hproj
  refine ⟨t, ht, hS, hregular, s, F, N, K, A, G, g, hN, hNuniv, hFc, hF, hK,
    ?_, hKK0.space_eq.trans hK0s, hA0, hA1, hA2, hA3, hAint,
    hGF, hgc, hg, hgPL, hproj⟩
  exact fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩

end PoincareMT.M76
