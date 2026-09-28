import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.AxisGerms
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.VertexGerms
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Coordinates

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

namespace ChartCircleArrangementVertexPatch

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {r : M → ℝ} {p : M}

theorem sectorCoordinates_signedAxis (P : ChartCircleArrangementVertexPatch r p)
    (horizontal : Bool) (sign : ℝ) (i : Bool × Bool)
    (hi : (if (if horizontal then i.1 else i.2) then (1 : ℝ) else -1) = sign)
    (t : ℝ) :
    P.sectorCoordinates i (signedAxis horizontal 1 t) =
      P.productCoordinates (signedAxis horizontal sign t + P.center) := by
  change P.productCoordinates
    (sectorParameterEquiv P.center i (signedAxis horizontal 1 t)) = _
  congr 1
  rw [← hi]
  rcases i with ⟨i, j⟩
  cases horizontal <;> cases i <;> cases j <;>
    ext <;> simp [sectorParameterEquiv_apply, signedAxis]

end ChartCircleArrangementVertexPatch

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

theorem exists_edgeVertexParameters {p : M}
    (P : ChartCircleArrangementVertexPatch D.radius p)
    (hlocal : ∀ q ∈ P.carrier,
      q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ P.circles)
    (a : D.EdgeIndex) {t₀ d : ℝ} (hd : d ≠ 0)
    (hp : (D.edge a.1 a.2).map t₀ = p) :
    ∃ (horizontal : Bool) (sign δ : ℝ) (A : OpenPartialHomeomorph ℝ ℝ),
      (sign = 1 ∨ sign = -1) ∧ 0 < δ ∧ δ ≤ P.width ∧ A 0 = 0 ∧
      Icc 0 δ ⊆ A.source ∧ StrictMonoOn A A.source ∧
      ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
      (∀ t, A.symm t = sign * axisCoordinate horizontal (D.edgeVertexGerm P a t₀ d t)) ∧
      (∀ u ∈ Icc 0 δ, 0 ≤ A u ∧ A u < 1) ∧
      (∀ u ∈ Ioc 0 δ, 0 < A u ∧ A '' Icc 0 u = Icc 0 (A u)) ∧
      (∀ i : Bool × Bool,
        (if (if horizontal then i.1 else i.2) then (1 : ℝ) else -1) = sign →
        (∀ u ∈ Icc 0 δ,
          (D.edge a.1 a.2).map (t₀ + d * A u) =
            P.sectorCoordinates i (signedAxis horizontal 1 u)) ∧
        (∀ u ∈ Ioc 0 δ,
          (fun t => (D.edge a.1 a.2).map (t₀ + d * t)) '' Icc 0 (A u) =
            (fun v => P.sectorCoordinates i (signedAxis horizontal 1 v)) '' Icc 0 u)) ∧
      (((t₀ = 0 ∧ d = 1) ∨ (t₀ = 1 ∧ d = -1)) →
        ∀ u ∈ Icc 0 δ, t₀ + d * A u ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨U, hU, hU0, hf, hf0, hreg, haxes⟩ :=
    D.exists_edgeVertexGerm_neighborhood P hlocal a hd hp
  let η : ℝ → M := fun t => (D.edge a.1 a.2).map (t₀ + d * t)
  have hη : Continuous η := (D.edge_contMDiff a).continuous.comp (by fun_prop)
  have hpC : p ∈ P.coordinates.target :=
    P.carrier_subset_target (P.openCarrier_subset_carrier P.mem_openCarrier)
  have hη0 : η 0 = p := by simpa [η] using hp
  let W := U ∩ (η ⁻¹' P.coordinates.target ∩ Ioo (-1 : ℝ) 1)
  have hW : IsOpen W := hU.inter ((P.coordinates.open_target.preimage hη).inter isOpen_Ioo)
  have hW0 : (0 : ℝ) ∈ W := ⟨hU0, by simpa only [mem_preimage, hη0] using hpC, by norm_num⟩
  have haxes' : ∀ᶠ t in 𝓝 0,
      (D.edgeVertexGerm P a t₀ d t).1 = 0 ∨ (D.edgeVertexGerm P a t₀ d t).2 = 0 :=
    Filter.mem_of_superset (hU.mem_nhds hU0) haxes
  obtain ⟨k, sign, δ₀, A, hsign, hδ₀, hA0, hsource, htarget, hmono,
      hsmooth, hinvsmooth, hinverse, haxis, himages⟩ :=
    exists_smooth_signed_axis_parametrization hW hW0 (hf.mono inter_subset_left)
      hf0 hreg haxes'
  let δ := min δ₀ P.width
  have hδ : 0 < δ := lt_min hδ₀ P.width_pos
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hsource' : Icc 0 δ ⊆ A.source := (Icc_subset_Icc_right hδle).trans hsource
  have hAzero : 0 ∈ A.source := hsource (left_mem_Icc.mpr hδ₀.le)
  have hbound (u : ℝ) (hu : u ∈ Icc 0 δ) : 0 ≤ A u ∧ A u < 1 := by
    have huA := hsource' hu
    refine ⟨?_, (htarget (A.map_source huA)).2.2.2⟩
    simpa only [hA0] using hmono.monotoneOn hAzero huA hu.1
  have hsurface (u : ℝ) (hu : u ∈ A.source) :
      η (A u) = P.productCoordinates (signedAxis k sign u + P.center) := by
    have hcoord := haxis u hu
    change collarParameterEquiv (P.coordinates.symm (η (A u))) - P.center =
      signedAxis k sign u at hcoord
    have hcoord' := sub_eq_iff_eq_add.mp hcoord
    change η (A u) = P.coordinates (collarParameterEquiv.symm
      (signedAxis k sign u + P.center))
    rw [← hcoord', collarParameterEquiv.symm_apply_apply,
      P.coordinates.right_inv (htarget (A.map_source hu)).2.1]
  refine ⟨k, sign, δ, A, hsign, hδ, min_le_right _ _, hA0, hsource',
    hmono, hsmooth, hinvsmooth, hinverse, hbound, ?_, ?_, ?_⟩
  · intro u hu
    have h := himages u ⟨hu.1, hu.2.trans hδle⟩
    exact ⟨h.1, h.2.1⟩
  · intro i hi
    have heq (u : ℝ) (hu : u ∈ Icc 0 δ) :
        η (A u) = P.sectorCoordinates i (signedAxis k 1 u) := by
      rw [P.sectorCoordinates_signedAxis k sign i hi]
      exact hsurface u (hsource' hu)
    refine ⟨heq, ?_⟩
    intro u hu
    have himage := (himages u ⟨hu.1, hu.2.trans hδle⟩).2.1
    rw [← himage, image_image]
    exact image_congr (fun v hv => heq v ⟨hv.1, hv.2.trans hu.2⟩)
  · intro hend u hu
    have hb := hbound u hu
    rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using ⟨hb.1, hb.2.le⟩
    · constructor <;> linarith [hb.1, hb.2]

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
