import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Reflection.PairChart
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeAffineHeightStep
import PoincareConjecture.Proofs.M76.Wall.Mathlib.CompatibleChartFormula
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts

set_option autoImplicit false
open Set Geometry Topology Metric

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem exists_centered_height_equiv (A : V3 →ₗ[ℝ] ℝ) (hA : A ≠ 0) :
    ∃ L : V3 ≃ᴬ[ℝ] C3, L 0 = 0 ∧ ∀ z, (L z).2 = A z := by
  obtain ⟨q, _, hq⟩ := ZeroChargeJoint.exists_affine_height_coordinates
    (E := P2) A.toAffineMap hA (by simp) 0
  let L := q.symm.trans (ContinuousAffineEquiv.constVAdd ℝ C3 (-q.symm 0))
  refine ⟨L, ?_, ?_⟩
  · change -q.symm 0 + q.symm 0 = 0
    exact neg_add_cancel _
  · intro z
    change -(q.symm 0).2 + (q.symm z).2 = A z
    rw [hq, hq]
    simp

theorem PLDomain.exists_original_boundary_pair_chart_of_proper_patch
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S T : Set X}
    (he : PLDomain e R) (hSR : S ⊆ R) (hTR : T ⊆ R)
    {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (w : C3 → X)
    (hw : PolyhedralPLInCharts e w
      ((Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r))
    (hwi : InjOn w ((Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r))
    (hwR : MapsTo w ((Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r) R)
    (hwfront : ∀ z ∈ (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r,
      w z ∈ frontier R ↔ z.2 = 0)
    (hwS : ∀ z ∈ (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r,
      w z ∈ S ↔ z.1.2 = 0)
    (hwT : ∀ z ∈ (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r,
      w z ∈ T ↔ z.1.1 = 0) :
    ∃ C : OriginalSurfacePairChart e S T (w 0) true,
      (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
      ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0 := by
  let D := (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (0 : ℝ) r
  have h0 : (0 : C3) ∈ D := by
    exact ⟨⟨⟨neg_nonpos.mpr hd.le, hd.le⟩, ⟨neg_nonpos.mpr hd.le, hd.le⟩⟩,
      le_rfl, hr.le⟩
  obtain ⟨B, A, hB0, hBzero, hA, hB, hBR, hBfront⟩ :=
    he.exists_centered_boundary_chart ((hwfront 0 h0).mpr rfl)
  obtain ⟨L, hL0, hLheight⟩ := exists_centered_height_equiv A hA
  have hpre := (hw.continuousOn 0 h0).preimage_mem_nhdsWithin (B.open_source.mem_nhds hB0)
  obtain ⟨eps, heps, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let b := min d (min r (eps / 2))
  have hb : 0 < b := lt_min hd (lt_min hr (half_pos heps))
  have hbd : b ≤ d := min_le_left _ _
  have hbr : b ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hbeps : b < eps := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self heps)
  let U := Icc (-b) b ×ˢ Icc (-b) b
  have hsub : U ×ˢ Icc (0 : ℝ) b ⊆ D := by
    intro z hz
    exact ⟨⟨⟨(neg_le_neg hbd).trans hz.1.1.1, hz.1.1.2.trans hbd⟩,
      ⟨(neg_le_neg hbd).trans hz.1.2.1, hz.1.2.2.trans hbd⟩⟩,
      hz.2.1, hz.2.2.trans hbr⟩
  have hmap : MapsTo w (U ×ˢ Icc (0 : ℝ) b) B.source := by
    intro z hz
    apply hsmall ⟨?_, hsub hz⟩
    rw [mem_ball_zero_iff, Prod.norm_def, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff, max_lt_iff]
    exact ⟨⟨((abs_le.mpr hz.1.1).trans_lt hbeps),
      ((abs_le.mpr hz.1.2).trans_lt hbeps)⟩,
      (abs_le.mpr ⟨(neg_nonpos.mpr hb.le).trans hz.2.1, hz.2.2⟩).trans_lt hbeps⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show -b < b by linarith)).prod
      (isFinitePLBallPair_Icc (show -b < b by linarith))
  obtain ⟨K, hK, hKs⟩ := J.exists_finite_interval_product hJ hb
  have hKU : K.space = U ×ˢ Icc (0 : ℝ) b := by rw [hKs, hJs]
  let f : C3 → C3 := L ∘ B ∘ w
  have hf : FinitePiecewiseAffineOn f (U ×ˢ Icc (0 : ℝ) b) := by
    rw [← hKU]
    exact (hw.finitePiecewiseAffineOn_compatible_chart B hB K hK
      (hKU.subset.trans hsub) (fun _ hz => hmap (hKU.subset hz))).postcomp L.toContinuousAffineMap
  have hfval (z : C3) : f z = L (B (w z)) := rfl
  have hfinv (z : C3) (hz : z ∈ U ×ˢ Icc (0 : ℝ) b) :
      B.symm (L.symm (f z)) = w z := by rw [hfval, L.symm_apply_apply, B.left_inv (hmap hz)]
  have hUint : (0 : P2) ∈ interior U := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨⟨neg_neg_of_pos hb, hb⟩, ⟨neg_neg_of_pos hb, hb⟩⟩
  have hRold (z : V3) (hz : z ∈ B.target) : B.symm z ∈ R ↔ 0 ≤ (L z).2 := by
    simpa only [hLheight, B.right_inv hz] using hBR _ (B.map_target hz)
  apply exists_original_boundary_pair_chart_of_halfbox B hB L hL0 hB0 hBzero hSR hTR
    hRold hb hUint f hf
  · intro z hz v hv heq
    exact hwi (hsub hz) (hsub hv) (B.injOn (hmap hz) (hmap hv) (L.injective heq))
  · rw [hfval, hBzero, hL0]
  · intro z hz
    rw [hfval, hLheight]
    exact (hBR _ (hmap hz)).mp (hwR (hsub hz))
  · intro z hz
    rw [hfval, hLheight, ← hBfront _ (hmap hz)]
    exact hwfront _ (hsub hz)
  · intro z hz
    rw [hfinv z hz]
    exact hwS _ (hsub hz)
  · intro z hz
    rw [hfinv z hz]
    exact hwT _ (hsub hz)

end PoincareConjecture.M76
