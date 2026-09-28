import PoincareConjecture.Proofs.M34.Standard.GeneralizedCompactMetricComparisonCoordinates
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateOperatorBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

private local instance : TopologicalSpace C.limit.carrier.carrier :=
  C.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier :=
  C.limit.carrier.isManifold

private theorem eventually_chart_pullback_inner_comparison
    (q : C.limit.sliceCarrier.carrier)
    {H : Set (EuclideanSpace ℝ (Fin 3))} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) q).target)
    (t : ℝ) (ht : t ∈ J) {delta : ℝ}
    (hdelta : 0 < delta) (_hdelta_lt : delta < 1) :
    ∀ᶠ k : ℕ in atTop,
      (extChartAt (𝓡 3) q).symm '' H ⊆ C.exhaustion.space k ∧
      t ∈ Icc (-C.exhaustion.time k) 0 ∧
      ∀ y ∈ H, ∀ v : EuclideanSpace ℝ (Fin 3),
        ∀ htk : t ∈ Icc (-C.exhaustion.time k) 0,
        (1 - delta) * (C.limit.flow.metric t).inner
            ((extChartAt (𝓡 3) q).symm y)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v) ≤
          (C.embedding k).pullbackInner t htk
            ((extChartAt (𝓡 3) q).symm y)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v) ∧
        (C.embedding k).pullbackInner t htk
            ((extChartAt (𝓡 3) q).symm y)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v) ≤
          (1 + delta) * (C.limit.flow.metric t).inner
            ((extChartAt (𝓡 3) q).symm y)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y) v) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let c := extChartAt (𝓡 3) q
  let g := C.limit.flow.metric t
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
  have hdom : ({t} ×ˢ H) ⊆ {p | p ∈ blowupMetricChartDomain C.limit q ∧
      c.symm p.2 ∈ C.exhaustion.space j} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    rcases mem_singleton_iff.mp hs with rfl
    exact ⟨⟨ht, hHt hy⟩, hj ⟨y, hy, rfl⟩⟩
  let eps := a * delta / 18
  have heps : 0 < eps := by positivity
  obtain ⟨N, hjN, hN⟩ := C.pullback_metric_CInfinity q j 0 ({t} ×ˢ H)
    (isCompact_singleton.prod hH) hdom eps heps
  have htimeSub := C.exhaustion.time_cofinal {t} isCompact_singleton
      (singleton_subset_iff.mpr ht)
  have htime : ∀ᶠ k : ℕ in atTop, t ∈ Icc (-C.exhaustion.time k) 0 :=
    htimeSub.mono (fun k hk => hk (by simp))
  filter_upwards [eventually_ge_atTop N, htime] with k hk htk
  refine ⟨hj.trans (C.exhaustion.space_increasing (hjN.trans hk)), htk, ?_⟩
  intro y hy v htk'
  let A := mfderiv (𝓡 3) (𝓡 3) c.symm y
  let f := (C.embedding k).forward t htk'
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
        ((S.base (C.subsequence k)).1 + t / S.scale (C.subsequence k))).inner
          (f (c.symm y))).bilinearComp D D
  have hentry (i l : Fin 3) :
      ‖(Bk - B y) (PiLp.single 2 i 1) (PiLp.single 2 l 1)‖ ≤ eps := by
    have he := (hN k hk).2 i l (t, y) ⟨rfl, hy⟩
    have he' : |blowupPullbackCoefficient (C.embedding k) q i l (t, y) -
        C.limit.carrier.coordinateCoefficient q
          (fun s x u w => (C.limit.flow.metric s).inner x u w) i l (t, y)| < eps := by
      simpa only [← dist_eq_norm, dist_iteratedFDerivWithin_zero, Real.dist_eq] using he
    change |(C.embedding k).pullbackInner t htk' (c.symm y)
        (A (PiLp.single 2 i 1)) (A (PiLp.single 2 l 1)) -
      g.inner (c.symm y) (A (PiLp.single 2 i 1)) (A (PiLp.single 2 l 1))| ≤ eps
    simpa only [blowupPullbackCoefficient, dif_pos htk',
      FlowCarrier.coordinateCoefficient, EuclideanSpace.basisFun_apply] using he'.le
  have hnorm : ‖Bk - B y‖ ≤ a * delta / 2 := by
    have hb := (Bk - B y).opNorm_le_card_mul_of_coordinates
      (fun i => ((Bk - B y) (PiLp.single 2 i 1)).opNorm_le_card_mul_of_coordinates
        (hentry i))
    norm_num only [Fintype.card_fin] at hb
    convert hb using 1
    ring
  have herr : |Bk v v - B y v v| ≤ (a * delta / 2) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖Bk - B y‖ * ‖v‖ * ‖v‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          (Bk - B y).le_opNorm₂ v v
      _ ≤ (a * delta / 2) * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)) (norm_nonneg v)
      _ = (a * delta / 2) * ‖v‖ ^ 2 := by ring
  change (1 - delta) * B y v v ≤ Bk v v ∧
    Bk v v ≤ (1 + delta) * B y v v
  have hvlow : a * ‖v‖ ^ 2 ≤ B y v v := hlow y hy v
  have hBnonneg : 0 ≤ B y v v := (mul_nonneg ha.le (sq_nonneg ‖v‖)).trans hvlow
  constructor
  · nlinarith [(abs_le.mp herr).1, (abs_le.mp herr).2]
  · nlinarith [(abs_le.mp herr).1, (abs_le.mp herr).2]

theorem limitNoncollapse_generalized_compact_inner_comparison
    {K : Set C.limit.sliceCarrier.carrier} (hK : IsCompact K)
    (t : ℝ) (ht : t ∈ J) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta_lt : delta < 1) :
    ∀ᶠ k : ℕ in atTop,
      K ⊆ C.exhaustion.space k ∧
      t ∈ Icc (-C.exhaustion.time k) 0 ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        ∀ htk : t ∈ Icc (-C.exhaustion.time k) 0,
        (1 - delta) * (C.limit.flow.metric t).inner x v v ≤
          (C.embedding k).pullbackInner t htk x v v ∧
        (C.embedding k).pullbackInner t htk x v v ≤
          (1 + delta) * (C.limit.flow.metric t).inner x v v := by
  classical
  have hlocal (q : C.limit.sliceCarrier.carrier) :
      ∃ V : Set C.limit.sliceCarrier.carrier, V ∈ 𝓝 q ∧
        ∀ᶠ k : ℕ in atTop, ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
          ∀ htk : t ∈ Icc (-C.exhaustion.time k) 0,
          (1 - delta) * (C.limit.flow.metric t).inner x v v ≤
            (C.embedding k).pullbackInner t htk x v v ∧
          (C.embedding k).pullbackInner t htk x v v ≤
            (1 + delta) * (C.limit.flow.metric t).inner x v v := by
    let c := extChartAt (𝓡 3) q
    obtain ⟨H, hH, hqH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) q)
      (mem_extChartAt_target (I := 𝓡 3) q)
    let V := c.source ∩ c ⁻¹' H
    have hV : V ∈ 𝓝 q := inter_mem
      (extChartAt_source_mem_nhds (I := 𝓡 3) q)
      ((continuousAt_extChartAt (I := 𝓡 3) q).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hqH))
    refine ⟨V, hV, ?_⟩
    filter_upwards [eventually_chart_pullback_inner_comparison C q hH hHt t ht
      hdelta hdelta_lt] with k hk x hx v
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ H, c.symm y = x := by
      exact ⟨c x, (show c x ∈ H from hx.2), c.left_inv hx.1⟩
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hHt hy)
    obtain ⟨w, rfl⟩ := hi.surjective v
    exact hk.2.2 y hy w
  choose V hV hbound using hlocal
  obtain ⟨s, _, hcover⟩ := hK.elim_nhds_subcover V (fun q _ => hV q)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset hK
  have htimeSub := C.exhaustion.time_cofinal ({t} : Set ℝ) isCompact_singleton
    (singleton_subset_iff.mpr ht)
  have htime : ∀ᶠ k : ℕ in atTop, t ∈ Icc (-C.exhaustion.time k) 0 :=
    htimeSub.mono (fun k hk => hk (show t ∈ ({t} : Set ℝ) by simp))
  filter_upwards [s.eventually_all.mpr (fun q _ => hbound q),
    eventually_ge_atTop j,
    htime] with k hk hjk htk
  refine ⟨hj.trans (C.exhaustion.space_increasing hjk), htk, ?_⟩
  intro x hx v htk'
  obtain ⟨q, hqs, hxq⟩ : ∃ q ∈ s, x ∈ V q := by
    simpa only [mem_iUnion, exists_prop] using hcover hx
  exact hk q hqs x hxq v htk'

end PoincareConjecture.M47
