import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.AtlasPatch
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.Source
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_planar_annulus_boundary_pair_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) (hKs : K.space = Ann)
    {j : P2 → X} (hj : PolyhedralPLInCharts e j K.space)
    (hemb : Topology.IsEmbedding (fun z : K.space => j z))
    (hjR : MapsTo j K.space R)
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (z : K.space) (hz : j z ∈ frontier R) :
    ∃ C : OpenPartialHomeomorph X C3,
      j z ∈ C.source ∧ C.target = interior (CoordinateHalfBoxes.box 1) ∧ C (j z) = 0 ∧
      (∀ x ∈ C.source, x ∈ R ↔ 0 ≤ (C x).1.1) ∧
      (∀ x ∈ C.source, x ∈ j '' K.space ↔ 0 ≤ (C x).1.1 ∧ (C x).2 = 0) ∧
      ∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans C) ((e i).symm.trans C).source ∧
        LocallyPiecewiseAffineOn (C.symm.trans (e i)) (C.symm.trans (e i)).source := by
  classical
  obtain ⟨H, B, hzH, hHz, hB, _, hHi, hhalf, hboundary⟩ :=
    exists_planar_annulus_boundary_chart (hKs.subset z.property) ((hproper z z.property).mp hz)
  let L : P2 ≃L[ℝ] V2 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H' := H.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hHs : H'.source = H.source := by
    change H.source ∩ H ⁻¹' (univ : Set P2) = H.source
    rw [preimage_univ, inter_univ]
  have hHz' : H' z = 0 := by
    change L (H z) = 0
    rw [hHz, map_zero]
  have hHi' : LocallyPiecewiseAffineOn H'.symm H'.target :=
    hHi.comp (locallyPiecewiseAffineOn_affine
      L.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ)
  let B' : V2 →ₗ[ℝ] ℝ := B.comp L.symm.toLinearMap
  have hB' : B' ≠ 0 := by
    intro hzero
    apply hB
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun A : V2 →ₗ[ℝ] ℝ => A (L x)) hzero
    change B (L.symm (L x)) = 0 at hx
    simpa only [L.symm_apply_apply, LinearMap.zero_apply] using hx
  have hBval (x : P2) : B' (H' x) = B (H x) := by
    change B (L.symm (L (H x))) = B (H x)
    rw [L.symm_apply_apply]
  have hhalf' (x : P2) (hx : x ∈ H'.source) : x ∈ K.space ↔ 0 ≤ B' (H' x) := by
    rw [hKs, hBval]
    exact hhalf x (hHs.subset hx)
  obtain ⟨G, A, hzG, hGz, hA, hcompat, hRhalf, hRfront⟩ := he.exists_centered_boundary_chart hz
  have hpositive (x : P2) (hx : x ∈ K.space) (hxG : j x ∈ G.source) :
      0 ≤ A (G (j x)) := (hRhalf (j x) hxG).mp (hjR hx)
  have hzero (x : P2) (hx : x ∈ K.space) (hxH : x ∈ H'.source)
      (hxG : j x ∈ G.source) : A (G (j x)) = 0 ↔ B' (H' x) = 0 := by
    rw [hBval]
    exact (hRfront (j x) hxG).symm.trans
      ((hproper x hx).trans (hboundary x (hHs.subset hxH)))
  obtain ⟨C, hzC, hCG, hCt, hCz, hCA, hCS, hCPL⟩ :=
    exists_original_boundary_source_pair_chart K hK hj hemb z H'
      (hHs.symm.subset hzH) hHz' hHi' B' hB' hhalf'
      G hcompat hzG hGz A hA hpositive hzero
  exact ⟨C, hzC, hCt, hCz, fun x hx =>
    (hRhalf x (hCG hx)).trans (hCA x hx), hCS, hCPL⟩

end PoincareConjecture.M76.Dehn
