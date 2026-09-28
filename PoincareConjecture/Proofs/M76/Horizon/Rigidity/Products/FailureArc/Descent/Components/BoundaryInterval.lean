import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.BranchCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.AxisMembership
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalEndpoint
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false
open Set Metric Geometry Topology Filter
open scoped Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem RawSourceCrossing.exists_boundary_interval_germ
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {a b : E}
    (C : RawSourceCrossing e f S R a b) (hf : PolyhedralPLInCharts e f S)
    (hR : MapsTo f S R) (side : Bool) (x : S)
    (hx : (x : E) ∈ if side then C.right else C.left)
    (hxG : (x : E) ∈ doubleLocusOn f S) (hxfront : f x ∈ frontier R) :
    ∃ D Q : Set E, IsFinitePLBallPair ℝ D Q ∧ (x : E) ∈ Q ∧
      D ⊆ doubleLocusOn f S ∧ ∀ᶠ z in 𝓝 (x : E), z ∈ doubleLocusOn f S ↔ z ∈ D := by
  let B := if side then C.right else C.left
  have hBS : B ⊆ S := by cases side <;> first | exact C.left_subset | exact C.right_subset
  have hBo : IsOpen ((Subtype.val : S → E) ⁻¹' B) := by
    cases side <;> first | exact C.left_open | exact C.right_open
  have hBe : IsEmbedding (fun z : B ↦ f z) := by
    cases side <;> first | exact C.left_embedding | exact C.right_embedding
  have hBT := C.branch_mapsTo_chart side
  have hxT : f x ∈ C.chart.source := hBT hx
  have hxaxis := (C.mem_double_iff_axis hR x.property hxT).mp hxG
  obtain ⟨N, V, hN, hNB, hV, hxV, hVN, _, H, _, hHi, hHval, hHback⟩ :=
    C.exists_finite_branch_coordinates hf side x hx
  have hNS : N.space ⊆ S := hNB.trans hBS
  have hcoordemb : IsEmbedding (fun z : B ↦ C.chart (f z)) :=
    C.chart.isEmbedding_restrict.comp (hBe.codRestrict _ (fun z ↦ hBT z.property))
  have hVo : IsOpen ((fun z : B ↦ (⟨z, hBS z.property⟩ : S)) ⁻¹' V) :=
    hV.preimage (continuous_subtype_val.subtype_mk _)
  obtain ⟨W, hW, hWV⟩ := hcoordemb.isInducing.isOpen_iff.mp hVo
  have hxW : C.chart (f x) ∈ W := hWV.symm.subset
    (show (⟨x, hx⟩ : B) ∈ (fun z : B ↦ (⟨z, hBS z.property⟩ : S)) ⁻¹' V from hxV)
  have hboundary := C.region.resolve_left (fun h => hxfront.2 (h hxT))
  have hheight : C.chart (f x) 2 = 0 := (hboundary.2 _ hxT).mp hxfront
  let O := W ∩ C.chart.target
  have hO : IsOpen O := hW.inter C.chart.open_target
  have hxO : C.chart (f x) ∈ O := ⟨hxW, C.chart.map_source hxT⟩
  let axis : ℝ →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun i : Fin 3 ↦
    if i = 2 then ContinuousLinearMap.id ℝ ℝ else 0).toContinuousAffineMap
  have haxis (t : ℝ) (i : Fin 3) : axis t i = if i = 2 then t else 0 := by
    by_cases hi : i = 2 <;> simp [axis, hi]
  have hinj : Function.Injective axis := fun u v h ↦ by
    have hh := congrArg (fun z : V3 ↦ z 2) h
    simpa only [haxis, if_true] using hh
  have haxisback {z : V3} (h0 : z 0 = 0) (h1 : z 1 = 0) : axis (z 2) = z := by
    ext i
    fin_cases i <;> simp [haxis, h0, h1]
  have hat : axis 0 = C.chart (f x) := by simpa only [hheight] using haxisback hxaxis.1 hxaxis.2
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp (hO.preimage axis.continuous) 0
    (show axis 0 ∈ O from hat.symm ▸ hxO)
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεO {u : ℝ} (hu : u ∈ Icc (0 : ℝ) ε) : axis u ∈ O := by
    apply hδO
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> dsimp only [ε] at * <;> linarith [hu.1, hu.2]
  have haxisN {u : ℝ} (hu : u ∈ Icc (0 : ℝ) ε) :
      axis u ∈ (C.chart ∘ f) '' N.space := by
    have huO := hεO hu
    have hregion : C.chart.symm (axis u) ∈ R := (hboundary.1 _ (C.chart.map_target huO.2)).mpr (by
      rw [C.chart.right_inv huO.2, haxis]
      exact hu.1)
    obtain ⟨z, hzB, hzeq⟩ := C.branch_axis_surjective side huO.2
      (by simp [haxis]) (by simp [haxis]) hregion
    have hzV : (⟨z, hBS hzB⟩ : S) ∈ V :=
      hWV.subset (show (⟨z, hzB⟩ : B) ∈ (fun z : B ↦ C.chart (f z)) ⁻¹' W from
        (show C.chart (f z) ∈ W from hzeq.symm ▸ huO.1))
    exact ⟨z, hVN ⟨⟨z, hBS hzB⟩, hzV, rfl⟩, hzeq⟩
  obtain ⟨q, hq, hqval⟩ := hHi
  have hqinj : InjOn q ((C.chart ∘ f) '' N.space) := by
    intro u hu v hv huv
    exact congrArg Subtype.val (H.symm.injective (Subtype.ext
      ((hqval ⟨u, hu⟩).trans (huv.trans (hqval ⟨v, hv⟩).symm))))
  have hqN {z : V3} (hz : z ∈ (C.chart ∘ f) '' N.space) : q z ∈ N.space := by
    rw [← hqval ⟨z, hz⟩]
    exact (H.symm ⟨z, hz⟩).property
  have hqback {z : V3} (hz : z ∈ (C.chart ∘ f) '' N.space) : C.chart (f (q z)) = z := by
    rw [← hqval ⟨z, hz⟩]
    exact hHback ⟨z, hz⟩
  have hxN : (x : E) ∈ N.space := hVN ⟨x, hxV, rfl⟩
  have hqt : q (axis 0) = x := by
    have hxH := hHval ⟨x, hxN⟩
    have htN := haxisN (show (0 : ℝ) ∈ Icc 0 ε by exact ⟨le_rfl, hε.le⟩)
    have heq : (⟨axis 0, htN⟩ : (C.chart ∘ f) '' N.space) = H ⟨x, hxN⟩ :=
      Subtype.ext (hat.trans hxH.symm)
    rw [← hqval ⟨axis 0, htN⟩, heq, H.symm_apply_apply]
  let J := axis '' Icc (0 : ℝ) ε
  have hJ : J ⊆ (C.chart ∘ f) '' N.space := by rintro z ⟨u, hu, rfl⟩; exact haxisN hu
  have hinterval := (isFinitePLBallPair_affine_interval hε
    axis hinj.injOn).image_of_subset hq hJ hqinj
  have hJG : q '' J ⊆ doubleLocusOn f S := by
    rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have hqB := hNB (hqN (haxisN hu))
    apply (C.mem_double_iff_axis hR (hBS hqB) (hBT hqB)).mpr
    rw [hqback (haxisN hu)]
    constructor <;> simp [haxis]
  have hxI : (x : E) ∈ q '' {axis 0, axis ε} := ⟨axis 0, Or.inl rfl, hqt⟩
  let Vnear : Set S := (Subtype.val ⁻¹' B) ∩ (fun z : S ↦ f z) ⁻¹'
    (C.chart.source ∩ C.chart ⁻¹' {z : V3 | |z 2| < ε})
  have hVnear : IsOpen Vnear := hBo.inter
    ((C.chart.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)).preimage
      hf.continuousOn.domRestrict)
  have hxnear : x ∈ Vnear := ⟨hx, hxT, by
    change |C.chart (f x) 2| < ε
    simpa only [hheight, abs_zero] using hε⟩
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hVnear
  have hxU : (x : E) ∈ U := hUV.symm.subset hxnear
  refine ⟨q '' J, q '' {axis 0, axis ε}, hinterval, hxI, hJG, ?_⟩
  filter_upwards [hU.mem_nhds hxU] with z hzU
  constructor
  · intro hzG
    have hznear := hUV.subset (show (⟨z, hzG.1⟩ : S) ∈ Subtype.val ⁻¹' U from hzU)
    have hzaxis := (C.mem_double_iff_axis hR hzG.1 hznear.2.1).mp hzG
    let u := C.chart (f z) 2
    have hu : u ∈ Icc (0 : ℝ) ε := by
      have hh := abs_lt.mp (show |C.chart (f z) 2| < ε from hznear.2.2)
      exact ⟨(hboundary.1 _ hznear.2.1).mp (hR hzG.1), hh.2.le⟩
    have hqB := hNB (hqN (haxisN hu))
    refine ⟨axis u, ⟨u, hu, rfl⟩, ?_⟩
    exact congrArg Subtype.val (hcoordemb.injective
      (a₁ := ⟨q (axis u), hqB⟩) (a₂ := ⟨z, hznear.1⟩)
      ((hqback (haxisN hu)).trans (haxisback hzaxis.1 hzaxis.2)))
  · exact fun hz ↦ hJG hz

theorem RawSourceCrossing.exists_boundary_segment_germ
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {a b : E}
    (C : RawSourceCrossing e f S R a b) (hf : PolyhedralPLInCharts e f S)
    (hR : MapsTo f S R) (side : Bool) (x : S)
    (hx : (x : E) ∈ if side then C.right else C.left)
    (hxG : (x : E) ∈ doubleLocusOn f S) (hxfront : f x ∈ frontier R) :
    ∃ u : E, u ≠ x ∧
      ∀ᶠ z in 𝓝 (x : E), z ∈ doubleLocusOn f S ↔ z ∈ segment ℝ (x : E) u := by
  obtain ⟨D, Q, hD, hxQ, _, hnear⟩ := C.exists_boundary_interval_germ hf hR side x hx hxG hxfront
  obtain ⟨u, hu, hgerm⟩ := hD.exists_segment_germ_of_mem_boundary hxQ
  refine ⟨u, hu, ?_⟩
  filter_upwards [hnear, hgerm] with z hz hz'
  exact hz.trans hz'

end PoincareConjecture.M76.Dehn.Annuli
