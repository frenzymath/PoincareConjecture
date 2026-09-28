import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Germs.Coordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalEndpoint
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false
open Set Metric Geometry Topology Filter
open scoped Topology

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_source_intersection_boundary_germ
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (H : OpenPartialHomeomorph V3 C3) (hH : LocallyPiecewiseAffineOn H H.source)
    {S : Set X}
    (hS : ∀ z ∈ H.source, B.symm z ∈ S ↔ (H z).2 = 0 ∧ 0 ≤ (H z).1.2)
    (hwhole : ∀ z ∈ H.source, B.symm z ∈ g '' K.space ↔ (H z).1.1 = 0 ∧ 0 ≤ (H z).1.2)
    (x : K.space) (hxB : g x ∈ B.source) (hxH : B (g x) ∈ H.source)
    (hzero : H (B (g x)) = 0) :
    ∃ d rim : Set E, IsFinitePLBallPair ℝ d rim ∧ (x : E) ∈ rim ∧
      d ⊆ {z | z ∈ K.space ∧ g z ∈ S} ∧
      ∀ᶠ z in 𝓝 (x : E), (z ∈ K.space ∧ g z ∈ S) ↔ z ∈ d := by
  obtain ⟨N, U, hN, hNK, hU, hxU, hUN, hchart, hcoords, J, hJ, hJinv, hJval, hJback⟩ :=
    hg.exists_finite_composed_chart_coordinates K hK hgi B hB H hH x hxB hxH
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hge : IsEmbedding (fun z : K.space => g z) :=
    (hg.continuousOn.domRestrict.isClosedEmbedding
      (fun a b hab => Subtype.ext (hgi a.property b.property hab))).isEmbedding
  obtain ⟨W, hW, hWU⟩ := hge.isInducing.isOpen_iff.mp hU
  have hxW : g x ∈ W := hWU.symm.subset hxU
  let O := H.target ∩ H.symm ⁻¹' (B.target ∩ B.symm ⁻¹' W)
  have hO : IsOpen O := H.symm.isOpen_inter_preimage (B.symm.isOpen_inter_preimage hW)
  have hH0 : H.symm 0 = B (g x) := by rw [← hzero, H.left_inv hxH]
  have hzeroO : (0 : C3) ∈ O := by
    refine ⟨hzero ▸ H.map_source hxH, ?_⟩
    change H.symm 0 ∈ B.target ∩ B.symm ⁻¹' W
    rw [hH0]
    exact ⟨B.map_source hxB, by simpa only [mem_preimage, B.left_inv hxB] using hxW⟩
  let axis : ℝ →ᴬ[ℝ] C3 :=
    ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)).prod
      (0 : ℝ →L[ℝ] ℝ) |>.toContinuousAffineMap
  have haxis (t : ℝ) : axis t = ((0, t), 0) := rfl
  have hai : Function.Injective axis := fun u v h => congrArg (fun z : C3 => z.1.2) h
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp (hO.preimage axis.continuous) 0
    (show axis 0 ∈ O from hzeroO)
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have huO {u : ℝ} (hu : u ∈ Icc 0 ε) : axis u ∈ O := by
    apply hδO
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> dsimp only [ε] at * <;> linarith [hu.1, hu.2]
  have haxisN {u : ℝ} (hu : u ∈ Icc 0 ε) :
      axis u ∈ (H ∘ B ∘ g) '' N.space := by
    have hwo := huO hu
    have hwH : H.symm (axis u) ∈ H.source := H.map_target hwo.1
    have hwK : B.symm (H.symm (axis u)) ∈ g '' K.space :=
      (hwhole _ hwH).mpr (by rw [H.right_inv hwo.1]; exact ⟨rfl, hu.1⟩)
    obtain ⟨z, hzK, heq⟩ := hwK
    have hzB : g z ∈ B.source := heq.symm ▸ B.map_target hwo.2.1
    have hzcoord : H (B (g z)) = axis u := by
      rw [heq, B.right_inv hwo.2.1, H.right_inv hwo.1]
    have hzU : (⟨z, hzK⟩ : K.space) ∈ U := hWU.subset
      (show g z ∈ W from heq.symm ▸ hwo.2.2)
    exact ⟨z, hUN ⟨⟨z, hzK⟩, hzU, rfl⟩, hzcoord⟩
  obtain ⟨q, hq, hqval⟩ := hJinv
  have hqi : InjOn q ((H ∘ B ∘ g) '' N.space) := by
    intro u hu v hv heq
    exact congrArg Subtype.val (J.symm.injective (Subtype.ext
      ((hqval ⟨u, hu⟩).trans (heq.trans (hqval ⟨v, hv⟩).symm))))
  have hqN {z : C3} (hz : z ∈ (H ∘ B ∘ g) '' N.space) : q z ∈ N.space := by
    rw [← hqval ⟨z, hz⟩]
    exact (J.symm ⟨z, hz⟩).property
  have hqback {z : C3} (hz : z ∈ (H ∘ B ∘ g) '' N.space) : H (B (g (q z))) = z := by
    rw [← hqval ⟨z, hz⟩]
    exact hJback ⟨z, hz⟩
  have h0 : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, hε.le⟩
  have hxN : (x : E) ∈ N.space := hUN ⟨x, hxU, rfl⟩
  have hqzero : q (axis 0) = x := by
    have heq : (⟨axis 0, haxisN h0⟩ : (H ∘ B ∘ g) '' N.space) = J ⟨x, hxN⟩ :=
      Subtype.ext (hzero.symm.trans (hJval ⟨x, hxN⟩).symm)
    rw [← hqval ⟨axis 0, haxisN h0⟩, heq, J.symm_apply_apply]
  let segment := axis '' Icc 0 ε
  have hsegN : segment ⊆ (H ∘ B ∘ g) '' N.space := by
    rintro _ ⟨u, hu, rfl⟩
    exact haxisN hu
  have hball := (isFinitePLBallPair_affine_interval hε
    axis hai.injOn).image_of_subset hq hsegN hqi
  have hsubset : q '' segment ⊆ {z | z ∈ K.space ∧ g z ∈ S} := by
    rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have hzN := hqN (haxisN hu)
    have hc := hchart _ hzN
    refine ⟨hNK hzN, ?_⟩
    have hh := (hS _ hc.2).mpr (by rw [hqback (haxisN hu)]; exact ⟨rfl, hu.1⟩)
    rwa [B.left_inv hc.1] at hh
  have hcenter : (x : E) ∈ q '' {axis 0, axis ε} :=
    ⟨axis 0, Or.inl rfl, hqzero⟩
  let Near : Set K.space := (fun z => g z) ⁻¹'
    (B.source ∩ B ⁻¹' (H.source ∩ H ⁻¹' {z : C3 | |z.1.2| < ε}))
  have hNear : IsOpen Near := (B.isOpen_inter_preimage (H.isOpen_inter_preimage
    (isOpen_lt (by fun_prop) continuous_const))).preimage hg.continuousOn.domRestrict
  have hxNear : x ∈ Near := by
    refine ⟨hxB, hxH, ?_⟩
    change |(H (B (g x))).1.2| < ε
    rw [hzero]
    simpa using hε
  obtain ⟨T, hT, hTNear⟩ := isOpen_induced_iff.mp hNear
  have hxT : (x : E) ∈ T := hTNear.symm.subset hxNear
  refine ⟨q '' segment, q '' {axis 0, axis ε}, hball, hcenter, hsubset, ?_⟩
  filter_upwards [hT.mem_nhds hxT] with z hzT
  constructor
  · rintro ⟨hzK, hzS⟩
    have hc := hTNear.subset (show (⟨z, hzK⟩ : K.space) ∈ Subtype.val ⁻¹' T from hzT)
    have htarget : (H (B (g z))).1.1 = 0 ∧ 0 ≤ (H (B (g z))).1.2 :=
      (hwhole _ hc.2.1).mp (by
      rw [B.left_inv hc.1]
      exact mem_image_of_mem g hzK)
    have hfirst := htarget.1
    have hlast : (H (B (g z))).2 = 0 := ((hS _ hc.2.1).mp (by
      rwa [B.left_inv hc.1])).1
    let u := (H (B (g z))).1.2
    have hu : u ∈ Icc 0 ε := by
      have hh := abs_lt.mp (show |u| < ε from hc.2.2)
      exact ⟨htarget.2, hh.2.le⟩
    have haxisback : axis u = H (B (g z)) :=
      Prod.ext (Prod.ext hfirst.symm rfl) hlast.symm
    have hqchart := hchart _ (hqN (haxisN hu))
    refine ⟨axis u, ⟨u, hu, rfl⟩, ?_⟩
    apply hgi (hNK (hqN (haxisN hu))) hzK
    exact B.injOn hqchart.1 hc.1 (H.injOn hqchart.2 hc.2.1
      ((hqback (haxisN hu)).trans haxisback))
  · exact fun hz => hsubset hz

end PoincareConjecture.M76
