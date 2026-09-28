import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.FiniteSimplyConnectedDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.CompactSurfaceRimModel
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in
theorem exists_compact_original_simplyConnected_marked_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V3)
    {R S M : Set X} (he : PLDomain e R) (hS : IsCompact S)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ ell (T y) = 0 ∧ psi (T y) = 0))
    (hboundary : (S ∩ M).Nonempty) [SimplyConnectedSpace S] :
    ∃ (H : D ≃ₜ S) (j : V2 → X), PolyhedralPLInCharts e j D ∧
      Topology.IsEmbedding (fun z : D => j z) ∧
      (∀ z : D, j z = (H z : X)) ∧ j '' D = S ∧
      ∀ z : D, j z ∈ M ↔ (z : V2) ∈ Q := by
  classical
  obtain ⟨s, F, K, B, g, hFc, hFi, _, hK, hBK, _, hKs, hBs,
      hgPL, _, hFg, hgS, hpure, hcofaces, hlinks, hpolygons⟩ :=
    exists_compact_original_surface_rim_finite_incidence
      e he hS (hboundary.mono inter_subset_left) hlocal
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let HS : S ≃ₜ K.space :=
    (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn F S hFi)
      ((hFc.comp continuous_subtype_val).subtype_mk _)).trans
        (Homeomorph.setCongr hKs.symm)
  have hHS (x : S) : (HS x : s → ℝ × V3) = F x := rfl
  have hHSg (z : K.space) : (HS.symm z : X) = g z := by
    apply hFi (HS.symm z).property (hgS.subset (mem_image_of_mem g z.property))
    exact ((hHS (HS.symm z)).symm.trans
      (congrArg Subtype.val (HS.apply_symm_apply z))).trans (hFg z z.property).symm
  let : SimplyConnectedSpace K.space := HS.symm.toHomotopyEquiv.simplyConnectedSpace
  have hBne : B.space.Nonempty := by
    rw [hBs]
    exact hboundary.image F
  have hball := isFinitePLBallPair_of_simplyConnected_marked_surface
    K B hK hBK hpure (by convert! hlinks) hcofaces hpolygons hBne
  have hD : IsFinitePLBallPair (ℝ × ℝ) D Q :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨A, hA, hAB⟩ := hD.exists_homeomorph hball
  obtain ⟨a, haPL, haa⟩ := hA
  let H := A.trans HS.symm
  let j := g ∘ a
  have hjH (z : D) : j z = (H z : X) := by
    exact (congrArg g (haa z).symm).trans (hHSg (A z)).symm
  have hamap : MapsTo a D K.space := by
    intro y hy
    rw [← haa ⟨y, hy⟩]
    exact (A ⟨y, hy⟩).property
  have hjPL : PolyhedralPLInCharts e j D := by
    obtain ⟨P, hP, hPs, hPa⟩ := haPL
    rw [← hPs]
    exact hgPL.comp_finitePiecewiseAffineOn P hP ⟨P, hP, rfl, hPa⟩
      (by simpa only [hPs] using hamap)
  have hjemb : Topology.IsEmbedding (fun z : D => j z) := by
    have hemb := (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : S → X)).comp
      H.isEmbedding
    simpa only [Function.comp_def, hjH] using hemb
  refine ⟨H, j, hjPL, hjemb, hjH, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hjH ⟨z, hz⟩]
      exact (H ⟨z, hz⟩).property
    · intro hx
      refine ⟨H.symm ⟨x, hx⟩, (H.symm ⟨x, hx⟩).property, ?_⟩
      rw [hjH, H.apply_symm_apply]
  · intro z
    have hmark : g (A z) ∈ M ↔ (A z : s → ℝ × V3) ∈ B.space := by
      rw [hBs]
      constructor
      · intro hM
        have hg : g (A z) ∈ S := hgS.subset (mem_image_of_mem g (A z).property)
        exact ⟨g (A z), ⟨hg, hM⟩, hFg (A z) (A z).property⟩
      · rintro ⟨x, hx, hFx⟩
        have heq := hFi hx.1 (hgS.subset (mem_image_of_mem g (A z).property))
          (hFx.trans (hFg (A z) (A z).property).symm)
        exact heq ▸ hx.2
    change g (a z) ∈ M ↔ (z : V2) ∈ Q
    rw [← haa z]
    exact hmark.trans (hAB z).symm

end PoincareConjecture.M76
