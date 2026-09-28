import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitMetricJets
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateOperatorBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedBlowupConvergence

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold




theorem eventually_chart_pullback_inner_comparison_zero
    (q : C.limit.sliceCarrier.carrier) {H : Set (EuclideanSpace ℝ (Fin 3))}
    (hH : IsCompact H) (hHt : H ⊆ (extChartAt (𝓡 3) q).target) :
    let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
      fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
    ∀ᶠ k : ℕ in atTop,
      (extChartAt (𝓡 3) q).symm '' H ⊆ C.exhaustion.space k ∧
      ∀ y ∈ H, ∀ v : EuclideanSpace ℝ (Fin 3),
        let A := mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y
        (1 / 2 : ℝ) * (C.limit.flow.metric 0).inner
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) ≤
          (C.embedding k).pullbackInner 0 (h0 k)
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) ∧
        (C.embedding k).pullbackInner 0 (h0 k)
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) ≤
          2 * (C.limit.flow.metric 0).inner
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  let c := extChartAt (𝓡 3) q
  let g := C.limit.flow.metric 0
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := g.pullbackCoefficients c.symm
  have hpos (y : E) (hy : y ∈ H) (v : E) (hv : v ≠ 0) : 0 < B y v v := by
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hHt hy)
    apply g.pos
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    convert! hz using 1
  obtain ⟨a, ha, hlow⟩ := exists_uniform_bilinear_lower_bound hH
    ((g.contDiffOn_chartCoefficients q).continuousOn.mono hHt) hpos
  have hcompact : IsCompact (c.symm '' H) :=
    hH.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hHt)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset hcompact
  have hdom : ({0} ×ˢ H) ⊆ {p | p ∈ blowupMetricChartDomain C.limit q ∧
      c.symm p.2 ∈ C.exhaustion.space j} := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    rcases mem_singleton_iff.mp ht with rfl
    exact ⟨⟨C.limit.zero_mem, hHt hy⟩, hj ⟨y, hy, rfl⟩⟩
  obtain ⟨N, hjN, hN⟩ := C.pullback_metric_CInfinity q j 0 ({0} ×ˢ H)
    (isCompact_singleton.prod hH) hdom (a / 18) (by positivity)
  filter_upwards [eventually_ge_atTop N] with k hk
  refine ⟨(hj.trans (C.exhaustion.space_increasing (hjN.trans hk))), ?_⟩
  intro y hy v
  let A := mfderiv (𝓡 3) (𝓡 3) c.symm y
  let f := (C.embedding k).forward 0 (h0 k)
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (f (c.symm y))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (f (c.symm y))) := by
    unfold TangentSpace
    infer_instance
  let D : E →L[ℝ] TangentSpace (𝓡 3) (f (c.symm y)) :=
    (mfderiv (𝓡 3) (𝓡 3) f (c.symm y)).comp A
  let Bk : E →L[ℝ] E →L[ℝ] ℝ :=
    S.scale (C.subsequence k) •
      (((S.flow (C.subsequence k)).metric
        ((S.base (C.subsequence k)).1 + 0 / S.scale (C.subsequence k))).inner
          (f (c.symm y))).bilinearComp D D
  have hentry (i l : Fin 3) :
      ‖(Bk - B y) (PiLp.single 2 i 1) (PiLp.single 2 l 1)‖ ≤ a / 18 := by
    have he := (hN k hk).2 i l (0, y) ⟨rfl, hy⟩
    have he' : |blowupPullbackCoefficient (C.embedding k) q i l (0, y) -
        C.limit.carrier.coordinateCoefficient q
          (fun t x u w => (C.limit.flow.metric t).inner x u w) i l (0, y)| < a / 18 := by
      simpa only [← dist_eq_norm, dist_iteratedFDerivWithin_zero, Real.dist_eq] using he
    change |(C.embedding k).pullbackInner 0 (h0 k) (c.symm y)
        (A (PiLp.single 2 i 1)) (A (PiLp.single 2 l 1)) -
      g.inner (c.symm y) (A (PiLp.single 2 i 1)) (A (PiLp.single 2 l 1))| ≤ a / 18
    simpa only [blowupPullbackCoefficient, dif_pos (h0 k),
      FlowCarrier.coordinateCoefficient, EuclideanSpace.basisFun_apply] using he'.le
  have hnorm : ‖Bk - B y‖ ≤ a / 2 := by
    have hb := (Bk - B y).opNorm_le_card_mul_of_coordinates
      (fun i => ((Bk - B y) (PiLp.single 2 i 1)).opNorm_le_card_mul_of_coordinates
        (hentry i))
    norm_num only [Fintype.card_fin] at hb
    convert hb using 1
    ring
  have herr : |Bk v v - B y v v| ≤ (a / 2) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖Bk - B y‖ * ‖v‖ * ‖v‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          (Bk - B y).le_opNorm₂ v v
      _ ≤ (a / 2) * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)) (norm_nonneg v)
      _ = (a / 2) * ‖v‖ ^ 2 := by ring
  change (1 / 2 : ℝ) * B y v v ≤ Bk v v ∧ Bk v v ≤ 2 * B y v v
  have hvlow : a * ‖v‖ ^ 2 ≤ B y v v := hlow y hy v
  have hBnonneg : 0 ≤ B y v v := (mul_nonneg ha.le (sq_nonneg ‖v‖)).trans hvlow
  constructor <;> nlinarith [(abs_le.mp herr).1, (abs_le.mp herr).2]

end PoincareConjecture.GeneralizedBlowupConvergence
