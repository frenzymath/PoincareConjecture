import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.BranchCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.AxisMembership
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalGerm
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals



set_option autoImplicit false
open Set Metric Geometry Topology Filter
open scoped Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem RawSourceCrossing.exists_interior_interval_germ
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {a b : E}
    (C : RawSourceCrossing e f S R a b) (hf : PolyhedralPLInCharts e f S)
    (hR : MapsTo f S R) (side : Bool) (x : S)
    (hx : (x : E) ∈ if side then C.right else C.left)
    (hxG : (x : E) ∈ doubleLocusOn f S) (hxint : f x ∈ interior R) :
    ∃ D Q : Set E, IsFinitePLBallPair ℝ D Q ∧ (x : E) ∈ D \ Q ∧
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
  let O := W ∩ (C.chart.target ∩ C.chart.symm ⁻¹' interior R)
  have hO : IsOpen O := hW.inter (C.chart.isOpen_inter_preimage_symm isOpen_interior)
  have hxO : C.chart (f x) ∈ O :=
    ⟨hxW, C.chart.map_source hxT, by
      change C.chart.symm (C.chart (f x)) ∈ interior R
      rwa [C.chart.left_inv hxT]⟩
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
  let t := C.chart (f x) 2
  have hat : axis t = C.chart (f x) := haxisback hxaxis.1 hxaxis.2
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp (hO.preimage axis.continuous) t
    (show axis t ∈ O from hat.symm ▸ hxO)
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεO {u : ℝ} (hu : u ∈ Icc (t - ε) (t + ε)) : axis u ∈ O := by
    apply hδO
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> dsimp only [ε] at * <;> linarith [hu.1, hu.2]
  have haxisN {u : ℝ} (hu : u ∈ Icc (t - ε) (t + ε)) :
      axis u ∈ (C.chart ∘ f) '' N.space := by
    have huO := hεO hu
    obtain ⟨z, hzB, hzeq⟩ := C.branch_axis_surjective side huO.2.1
      (by simp [haxis]) (by simp [haxis]) (interior_subset huO.2.2)
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
  have hqt : q (axis t) = x := by
    have hxH := hHval ⟨x, hxN⟩
    have htN := haxisN (show t ∈ Icc (t - ε) (t + ε) by constructor <;> linarith)
    have heq : (⟨axis t, htN⟩ : (C.chart ∘ f) '' N.space) = H ⟨x, hxN⟩ :=
      Subtype.ext (hat.trans hxH.symm)
    rw [← hqval ⟨axis t, htN⟩, heq, H.symm_apply_apply]
  let J := axis '' Icc (t - ε) (t + ε)
  have hJ : J ⊆ (C.chart ∘ f) '' N.space := by rintro z ⟨u, hu, rfl⟩; exact haxisN hu
  have hinterval := (isFinitePLBallPair_affine_interval (by linarith : t - ε < t + ε)
    axis hinj.injOn).image_of_subset hq hJ hqinj
  have hJG : q '' J ⊆ doubleLocusOn f S := by
    rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have hqB := hNB (hqN (haxisN hu))
    apply (C.mem_double_iff_axis hR (hBS hqB) (hBT hqB)).mpr
    rw [hqback (haxisN hu)]
    constructor <;> simp [haxis]
  have hxI : (x : E) ∈ q '' J \ q '' {axis (t - ε), axis (t + ε)} := by
    refine ⟨⟨axis t, ⟨t, by constructor <;> linarith, rfl⟩, hqt⟩, ?_⟩
    rintro ⟨z, hz, hzq⟩
    have htN := haxisN (show t ∈ Icc (t - ε) (t + ε) by constructor <;> linarith)
    rcases hz with rfl | rfl
    · have he := hinj (hqinj (haxisN ⟨le_rfl, by linarith⟩) htN (hzq.trans hqt.symm))
      linarith
    · have he := hinj (hqinj (haxisN ⟨by linarith, le_rfl⟩) htN (hzq.trans hqt.symm))
      linarith
  let Vnear : Set S := (Subtype.val ⁻¹' B) ∩ (fun z : S ↦ f z) ⁻¹'
    (C.chart.source ∩ C.chart ⁻¹' {z : V3 | |z 2 - t| < ε})
  have hVnear : IsOpen Vnear := hBo.inter
    ((C.chart.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)).preimage
      hf.continuousOn.domRestrict)
  have hxnear : x ∈ Vnear := ⟨hx, hxT, by simpa [t] using hε⟩
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hVnear
  have hxU : (x : E) ∈ U := hUV.symm.subset hxnear
  refine ⟨q '' J, q '' {axis (t - ε), axis (t + ε)}, hinterval, hxI, hJG, ?_⟩
  filter_upwards [hU.mem_nhds hxU] with z hzU
  constructor
  · intro hzG
    have hznear := hUV.subset (show (⟨z, hzG.1⟩ : S) ∈ Subtype.val ⁻¹' U from hzU)
    have hzaxis := (C.mem_double_iff_axis hR hzG.1 hznear.2.1).mp hzG
    let u := C.chart (f z) 2
    have hu : u ∈ Icc (t - ε) (t + ε) := by
      have hh := abs_lt.mp (show |C.chart (f z) 2 - t| < ε from hznear.2.2)
      constructor <;> dsimp only [u] <;> linarith [hh.1, hh.2]
    have hqB := hNB (hqN (haxisN hu))
    refine ⟨axis u, ⟨u, hu, rfl⟩, ?_⟩
    exact congrArg Subtype.val (hcoordemb.injective
      (a₁ := ⟨q (axis u), hqB⟩) (a₂ := ⟨z, hznear.1⟩)
      ((hqback (haxisN hu)).trans (haxisback hzaxis.1 hzaxis.2)))
  · exact fun hz ↦ hJG hz

theorem RawSourceCrossing.exists_interior_two_segment_germ
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {a b : E}
    (C : RawSourceCrossing e f S R a b) (hf : PolyhedralPLInCharts e f S)
    (hR : MapsTo f S R) (side : Bool) (x : S)
    (hx : (x : E) ∈ if side then C.right else C.left)
    (hxG : (x : E) ∈ doubleLocusOn f S) (hxint : f x ∈ interior R) :
    ∃ u v : E, u ≠ x ∧ v ≠ x ∧ segment ℝ (x : E) u ∩ segment ℝ (x : E) v ⊆ {(x : E)} ∧
      ∀ᶠ z in 𝓝 (x : E), z ∈ doubleLocusOn f S ↔ z ∈ segment ℝ (x : E) u ∪ segment ℝ (x : E) v := by
  obtain ⟨D, Q, hD, hxD, _, hnear⟩ := C.exists_interior_interval_germ hf hR side x hx hxG hxint
  obtain ⟨u, v, hu, hv, hinter, hgerm⟩ := hD.exists_two_segment_germ hxD
  refine ⟨u, v, hu, hv, hinter, ?_⟩
  filter_upwards [hnear, hgerm] with z hz hz'
  exact hz.trans hz'

end PoincareConjecture.M76.Dehn.Annuli
