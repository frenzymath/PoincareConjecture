import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CompressedPhaseModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Incidence.PhaseCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Incidence.IntrinsicMarkedSubdivision









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

open Classical in


theorem exists_compressed_sourceSurface_incidence_model
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
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K J : SimplicialComplex ℝ (s → ℝ × V3))
      (Hmodel : K.space ≃ₜ sourceSurface phi theta) (g : (s → ℝ × V3) → X),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F R ∧ K.faces.Finite ∧ J ≤ K ∧ J.faces.Finite ∧
      K.space = F '' sourceSurface phi theta ∧
      J.space = F '' (sourceSurface phi theta ∩ frontier R) ∧
      (∀ x : sourceSurface phi theta, (Hmodel.symm x : s → ℝ × V3) = F x) ∧
      (∀ z : K.space, (Hmodel z : X) = g z) ∧
      PolyhedralPLInCharts e g K.space ∧
      (∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ J.space) ∧
      (∀ t ∈ K.faces, (∀ w ∈ t, w ∈ J.vertices) → t ∈ J.faces) ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ J.faces then 1 else 2) ∧
      (∀ w ∈ K.vertices, IsConnected (K.link w).space) ∧
      (sourceSurface phi theta).Nonempty := by
  classical
  obtain ⟨s, F, N, K0, A, G, gN, _, hRNint, hFc, hF, _, hA, _,
    _, _, hA2, hA3, _, hGF, _, hgG, hgPL, hSne, _⟩ :=
    exists_compressed_sourceSurface_finite_marked_model e d phi hphi F0 heN hfront hAB hcorner
  have hRN : R ⊆ N := hRNint.trans interior_subset
  have hSN : sourceSurface phi theta ⊆ N := (sourceSurface_subset phi theta).trans hRN
  have hFi : InjOn F N := by
    intro x hx y hy hxy
    have hh : G ⟨x, hx⟩ = G ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hGF, hGF]
      exact hxy
    exact congrArg Subtype.val (G.injective hh)
  let g : (s → ℝ × V3) → X := fun z => gN z
  have hgF (x : X) (hx : x ∈ N) : g (F x) = x := by
    have hh := hgG (G ⟨x, hx⟩)
    rw [G.symm_apply_apply] at hh
    simpa only [hGF] using hh
  let f : sourceSurface phi theta → (A 2).space := fun x =>
    ⟨F x, hA2.symm ▸ mem_image_of_mem F x.property⟩
  have hf : Continuous f := (hFc.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hFi (hSN x.property) (hSN y.property) (congrArg Subtype.val hxy))
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨x, hx, hxz⟩ := hA2.subset z.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  let : CompactSpace (sourceSurface phi theta) :=
    isCompact_iff_compactSpace.mp (sourceSurface_isCompact phi theta)
  let H0 : (A 2).space ≃ₜ sourceSurface phi theta :=
    (hf.isClosedEmbedding hfi |>.isEmbedding.toHomeomorphOfSurjective hfs).symm
  have hH0F (x : sourceSurface phi theta) : (H0.symm x : s → ℝ × V3) = F x := rfl
  have hFH0 (z : (A 2).space) : F (H0 z) = z := by
    rw [← hH0F, H0.symm_apply_apply]
  have hH0 (z : (A 2).space) : (H0 z : X) = g z := by
    rw [← hFH0 z, hgF _ (hSN (H0 z).property)]
  have hgS (z : (A 2).space) : g z ∈ sourceSurface phi theta := by
    rw [← hH0]
    exact (H0 z).property
  have hFg (z : (A 2).space) : F (g z) = z := by
    rw [← hH0]
    exact hFH0 z
  have hA32 : (A 3).space ⊆ (A 2).space := by
    rw [hA3, hA2]
    exact image_mono inter_subset_left
  have hgPL2 : PolyhedralPLInCharts e g (A 2).space :=
    hgPL.restrict_finite (A 2) (hA 2).2.1
      (SimplicialComplex.space_subset_of_le (hA 2).1)
  have hmark (z : s → ℝ × V3) (hz : z ∈ (A 2).space) :
      g z ∈ frontier R ↔ z ∈ (A 3).space := by
    rw [hA3]
    constructor
    · intro h
      exact ⟨g z, ⟨hgS ⟨z, hz⟩, h⟩, hFg ⟨z, hz⟩⟩
    · rintro ⟨x, hx, hxz⟩
      have hEq : x = g z := hFi (hSN hx.1) (hSN (hgS ⟨z, hz⟩))
        (hxz.trans (hFg ⟨z, hz⟩).symm)
      exact hEq ▸ hx.2
  obtain ⟨K, J, hK, hKK, hBK, hBB, hfull, hpure, hcounts, hlinks⟩ :=
    exists_marked_surface_incidence_subdivision_of_intrinsic_mark
      e (A 2) (A 3) (hA 2).2.1 (hA 3).2.1 hA32 H0 g hH0 hgPL2 hmark
      (exists_compressed_sourceSurface_plane_halfplane_charts e phi heN hfront hAB hcorner)
  let Hmodel : K.space ≃ₜ sourceSurface phi theta :=
    (Homeomorph.setCongr hKK.space_eq).trans H0
  refine ⟨s, F, K, J, Hmodel, g, hFc, hF, hFi.mono hRN, hK, hBK,
    hK.subset hBK, hKK.space_eq.trans hA2, hBB.trans hA3, ?_, ?_, ?_, ?_,
    hfull, hpure, hcounts, hlinks, hSne⟩
  · exact hH0F
  · intro z
    exact hH0 ⟨z, hKK.space_eq ▸ z.property⟩
  · exact hKK.space_eq.symm ▸ hgPL2
  · intro z hz
    rw [hBB]
    exact hmark z (hKK.space_eq ▸ hz)

end PoincareConjecture.M76.HamiltonIntervalTorus
