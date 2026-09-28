import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M39.Mathlib.BilinearComparison










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M39

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

section Coefficients

variable {A B : GeneralizedSliceCarrier.{u}}
  {g : ℝ → RiemannianMetric 3 A.carrier}
  {gT : RiemannianMetric 3 B.carrier}
  {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}




theorem metricLimit_eventually_coefficient_bound
    (hlim : SurgeryMetricLimitOn A B g gT f U T)
    {q : A.carrier} (hq : q ∈ U) {K : Set E₃} (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 3) q).target)
    (hU : (extChartAt (𝓡 3) q).symm '' K ⊆ U)
    (a b : Fin 3) {e : ℝ} (he : 0 < e) :
    ∀ᶠ t in 𝓝[<] T, ∀ p ∈ K,
      ‖(gT.pullbackCoefficients (f ∘ (extChartAt (𝓡 3) q).symm) p -
        (g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm p)
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)‖ ≤ e := by
  obtain ⟨d, hd, hbound⟩ := hlim q hq K hK hchart hU 0 a b e he
  apply mem_nhdsLT_iff_exists_Ioo_subset.mpr
  refine ⟨T - d, sub_lt_self T hd, fun t ht p hp => ?_⟩
  have h := hbound t ht.1 ht.2 p hp
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] at h
  have hcoeff :
      ‖(gT.pullbackCoefficients (f ∘ (extChartAt (𝓡 3) q).symm) p -
        (g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm p)
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)‖ =
        ‖surgeryMetricCoefficient gT (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b p -
          singularMetricCoefficient (g t) q a b p‖ := rfl
  rw [hcoeff, norm_sub_rev]
  exact h.le

end Coefficients

section ChartComparison

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier}
  (e : SurgeryRegionEquivalence A B U univ) (hU : IsOpen U)

include hU



theorem limitIdentification_mfderiv_injective {x : A.carrier} (hx : x ∈ U) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) e.map x) := by
  have hmap := (e.map_smooth x hx).contMDiffAt (hU.mem_nhds hx)
  have hinv := (contMDiffOn_univ.mp e.inverse_smooth).contMDiffAt
    (x := e.map x)
  have heq : e.inverse ∘ e.map =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact e.left_inverse hy
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x (hinv.mdifferentiableAt (by simp))
    (hmap.mdifferentiableAt (by simp)), mfderiv_id] at hd
  have hleft : Function.LeftInverse (mfderiv (𝓡 3) (𝓡 3) e.inverse (e.map x))
      (mfderiv (𝓡 3) (𝓡 3) e.map x) := by
    intro v
    exact congrArg (fun L => L v) hd
  exact hleft.injective




theorem limit_chart_coefficients_pos
    (gT : RiemannianMetric 3 B.carrier) (q : A.carrier) {p : E₃}
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hreg : (extChartAt (𝓡 3) q).symm p ∈ U)
    {v : E₃} (hv : v ≠ 0) :
    0 < gT.pullbackCoefficients (e.map ∘ (extChartAt (𝓡 3) q).symm) p v v := by
  have hchart := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp)
  have hmap := (e.map_smooth _ hreg).contMDiffAt (hU.mem_nhds hreg)
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓡 3) hp
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  have hchartinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3)
      (extChartAt (𝓡 3) q).symm p) := by
    have hleft : Function.LeftInverse (mfderiv (𝓡 3) (𝓡 3)
        (extChartAt (𝓡 3) q) ((extChartAt (𝓡 3) q).symm p))
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p) := by
      intro w
      exact congrArg (fun L => L w) hcomp
    exact hleft.injective
  change 0 < gT.inner _
    (mfderiv (𝓡 3) (𝓡 3) (e.map ∘ (extChartAt (𝓡 3) q).symm) p v)
    (mfderiv (𝓡 3) (𝓡 3) (e.map ∘ (extChartAt (𝓡 3) q).symm) p v)
  apply gT.pos
  rw [mfderiv_comp p (hmap.mdifferentiableAt (by simp))
    (hchart.mdifferentiableAt (by simp))]
  change mfderiv (𝓡 3) (𝓡 3) e.map ((extChartAt (𝓡 3) q).symm p)
    (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p v) ≠ 0
  intro hz
  apply hv
  have hzero : mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p v = 0 :=
    (injective_iff_map_eq_zero _).mp
      (limitIdentification_mfderiv_injective e hU hreg) _ hz
  exact (injective_iff_map_eq_zero _).mp hchartinj _ hzero




theorem metricLimit_eventually_chart_comparison
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier} {T : ℝ}
    (hlim : SurgeryMetricLimitOn A B g gT e.map U T)
    {q : A.carrier} (hq : q ∈ U) {K : Set E₃} (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 3) q).target)
    (hreg : (extChartAt (𝓡 3) q).symm '' K ⊆ U)
    {k : ℝ} (hk : 1 < k) :
    ∀ᶠ t in 𝓝[<] T, ∀ p ∈ K, ∀ v : E₃,
      gT.pullbackCoefficients (e.map ∘ (extChartAt (𝓡 3) q).symm) p v v ≤
        k * (g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm p v v := by
  apply ContinuousLinearMap.eventually_quadratic_le_mul_of_coefficients
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hK
  · intro p hp
    apply (gT.contDiffAt_pullbackCoefficients ?_).continuousAt.continuousWithinAt
    exact ((e.map_smooth _ (hreg ⟨p, hp, rfl⟩)).contMDiffAt
      (hU.mem_nhds (hreg ⟨p, hp, rfl⟩))).comp p
        ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hchart hp)))
  · intro p hp v hv
    exact limit_chart_coefficients_pos e hU gT q (hchart hp) (hreg ⟨p, hp, rfl⟩) hv
  · intro a b r hr
    exact metricLimit_eventually_coefficient_bound hlim hq hK hchart hreg a b hr
  · exact hk




theorem metric_comparison_of_chart_comparison
    (g : RiemannianMetric 3 A.carrier) (gT : RiemannianMetric 3 B.carrier)
    (q : A.carrier) {x : A.carrier} (hx : x ∈ (extChartAt (𝓡 3) q).source)
    (hreg : x ∈ U) {k : ℝ}
    (hbound : ∀ w : E₃,
      gT.pullbackCoefficients (e.map ∘ (extChartAt (𝓡 3) q).symm)
          ((extChartAt (𝓡 3) q) x) w w ≤
        k * g.pullbackCoefficients (extChartAt (𝓡 3) q).symm
          ((extChartAt (𝓡 3) q) x) w w)
    (v : TangentSpace (𝓡 3) x) :
    gT.inner (e.map x) (mfderiv (𝓡 3) (𝓡 3) e.map x v)
      (mfderiv (𝓡 3) (𝓡 3) e.map x v) ≤ k * g.inner x v v := by
  let c := extChartAt (𝓡 3) q
  have hcx : c.symm (c x) = x := c.left_inv hx
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (c.map_source hx))
  have he := (e.map_smooth _ (hcx.symm ▸ hreg)).contMDiffAt
    (hU.mem_nhds (hcx.symm ▸ hreg))
  have hderiv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 3) hx
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hderiv
  have hv : mfderiv (𝓡 3) (𝓡 3) c.symm (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v) = v := congrArg (fun L => L v) hderiv
  have hb := hbound (mfderiv (𝓡 3) (𝓡 3) c x v)
  change gT.inner (e.map (c.symm (c x)))
    (mfderiv (𝓡 3) (𝓡 3) (e.map ∘ c.symm) (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v))
    (mfderiv (𝓡 3) (𝓡 3) (e.map ∘ c.symm) (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v)) ≤
    k * g.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v)) at hb
  rw [mfderiv_comp (c x) (he.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))] at hb
  change gT.inner (e.map (c.symm (c x)))
    (mfderiv (𝓡 3) (𝓡 3) e.map (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v)))
    (mfderiv (𝓡 3) (𝓡 3) e.map (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v))) ≤
    k * g.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v)) at hb
  erw [hv, hcx] at hb
  exact hb




theorem metricLimit_eventually_local_comparison
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier} {T : ℝ}
    (hlim : SurgeryMetricLimitOn A B g gT e.map U T)
    {x : A.carrier} (hx : x ∈ U) {k : ℝ} (hk : 1 < k) :
    ∀ᶠ p in (𝓝[<] T) ×ˢ 𝓝 x, ∀ v : TangentSpace (𝓡 3) p.2,
      gT.inner (e.map p.2) (mfderiv (𝓡 3) (𝓡 3) e.map p.2 v)
        (mfderiv (𝓡 3) (𝓡 3) e.map p.2 v) ≤ k * (g p.1).inner p.2 v v := by
  let c := extChartAt (𝓡 3) x
  have hxchart : x ∈ c.source := mem_extChartAt_source x
  have htarget : c x ∈ c.target := c.map_source hxchart
  have hV : c.target ∩ c.symm ⁻¹' U ∈ 𝓝 (c x) := by
    apply ((contMDiffOn_extChartAt_symm (n := ∞) x).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓡 3) x) hU).mem_nhds
    refine ⟨htarget, ?_⟩
    change c.symm (c x) ∈ U
    rwa [c.left_inv hxchart]
  obtain ⟨K, hKnhds, hKsub, hK⟩ := local_compact_nhds hV
  have hchart : K ⊆ c.target := fun p hp => (hKsub hp).1
  have hreg : c.symm '' K ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hKsub hp).2
  have htime := metricLimit_eventually_chart_comparison e hU hlim hx hK hchart hreg hk
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ c y ∈ K := by
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hxchart,
      (continuousAt_extChartAt (I := 𝓡 3) x).preimage_mem_nhds hKnhds] with y hy hcy
    exact ⟨hy, hcy⟩
  filter_upwards [htime.prod_mk hnear] with p hp
  intro v
  have hy : p.2 ∈ U := by
    have hh := (hKsub hp.2.2).2
    simpa only [mem_preimage, c.left_inv hp.2.1] using hh
  exact metric_comparison_of_chart_comparison e hU (g p.1) gT x hp.2.1 hy
    (hp.1 (c p.2) hp.2.2) v




theorem metricLimit_eventually_compact_comparison
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier} {T : ℝ}
    (hlim : SurgeryMetricLimitOn A B g gT e.map U T)
    {K : Set A.carrier} (hK : IsCompact K) (hreg : K ⊆ U)
    {k : ℝ} (hk : 1 < k) :
    ∀ᶠ t in 𝓝[<] T, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      gT.inner (e.map x) (mfderiv (𝓡 3) (𝓡 3) e.map x v)
        (mfderiv (𝓡 3) (𝓡 3) e.map x v) ≤ k * (g t).inner x v v := by
  have h : ∀ᶠ p in (𝓝[<] T) ×ˢ 𝓝ˢ K, ∀ v : TangentSpace (𝓡 3) p.2,
      gT.inner (e.map p.2) (mfderiv (𝓡 3) (𝓡 3) e.map p.2 v)
        (mfderiv (𝓡 3) (𝓡 3) e.map p.2 v) ≤ k * (g p.1).inner p.2 v v :=
    hK.mem_prod_nhdsSet_of_forall (l := 𝓝[<] T)
      (fun x hx => metricLimit_eventually_local_comparison e hU hlim (hreg hx) hk)
  exact h.curry.mono (fun _ ht => ht.self_of_nhdsSet)

end ChartComparison

end PoincareConjecture.M39
