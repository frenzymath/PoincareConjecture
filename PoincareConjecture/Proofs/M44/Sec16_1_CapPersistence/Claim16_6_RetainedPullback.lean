import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedRicciEquation
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_GeodesicTransport
import PoincareConjecture.Proofs.M44.Mathlib.SmoothLocalFactorization










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance retainedPullbackBilinearNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance retainedPullbackBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T b : ℝ}



noncomputable def retainedPullbackCoefficients
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (A : E → (slice event.tMinus).carrier) (p : ℝ × E) : Bilin :=
  if p.1 < T then (event.pre_flow.metric p.1).pullbackCoefficients A p.2
  else (G.metric p.1).pullbackCoefficients (event.retention.map ∘ A) p.2




theorem retainedPullbackCoefficients_smooth_of_factorization
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (hbirth : G.metric T = metric T)
    (q : (slice event.tMinus).carrier) (hq : q ∈ interior event.retained_pre)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre)
    {A : E → (slice event.tMinus).carrier} {k : E → E}
    (hk : ContDiffOn ℝ ∞ k V) (hmap : MapsTo k V U)
    (hfactor : ∀ x ∈ V, A x = (extChartAt (𝓡 3) q).symm (k x)) :
    ContDiffOn ℝ ∞ (retainedPullbackCoefficients event G A) (Ioo event.tMinus b ×ˢ V) := by
  have hB := (retainedChartCoefficients_smooth_ricci event G hTb hbirth q hq hU hchart hret).1
  have hkprod : ContDiffOn ℝ ∞ (fun p : ℝ × E => (p.1, k p.2))
      (Ioo event.tMinus b ×ˢ V) :=
    contDiffOn_fst.prodMk (hk.comp contDiffOn_snd (fun _ hp => hp.2))
  have hbase : ContDiffOn ℝ ∞
      (fun p : ℝ × E => retainedChartCoefficients event G q (p.1, k p.2))
      (Ioo event.tMinus b ×ˢ V) :=
    hB.comp hkprod (fun _ hp => ⟨hp.1, hmap hp.2⟩)
  have hd : ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ k p.2)
      (Ioo event.tMinus b ×ˢ V) :=
    (hk.fderiv_of_isOpen hV (by simp)).comp contDiffOn_snd (fun _ hp => hp.2)
  have hflip : ContDiff ℝ ∞ (fun L : Bilin => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hpull : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      (retainedChartCoefficients event G q (p.1, k p.2)).bilinearComp
        (fderiv ℝ k p.2) (fderiv ℝ k p.2)) (Ioo event.tMinus b ×ˢ V) := by
    simpa only [ContinuousLinearMap.bilinearComp, Function.comp_def] using
      hflip.comp_contDiffOn ((hflip.comp_contDiffOn (hbase.clm_comp hd)).clm_comp hd)
  apply hpull.congr
  intro p hp
  have hkx := (hk.contDiffAt (hV.mem_nhds hp.2)).differentiableAt (by simp)
  have heq : (extChartAt (𝓡 3) q).symm ∘ k =ᶠ[𝓝 p.2] A := by
    filter_upwards [hV.mem_nhds hp.2] with y hy
    exact (hfactor y hy).symm
  ext v w
  by_cases ht : p.1 < T
  · have he := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds (hchart (hmap hp.2)))
    simpa only [retainedPullbackCoefficients, retainedChartCoefficients, if_pos ht,
      ContinuousLinearMap.bilinearComp_apply] using
      (event.pre_flow.metric p.1).pullbackCoefficients_eq_of_comp_germ
        (he.mdifferentiableAt (by simp)) hkx heq v w
  · have he := (retained_inverse_coordinates_smooth event q hchart hret).contMDiffAt
      (hU.mem_nhds (hmap hp.2))
    have heq' : (event.retention.map ∘ (extChartAt (𝓡 3) q).symm) ∘ k =ᶠ[𝓝 p.2]
        event.retention.map ∘ A := by
      filter_upwards [heq] with y hy
      exact congrArg event.retention.map hy
    simpa only [retainedPullbackCoefficients, retainedChartCoefficients, if_neg ht,
      ContinuousLinearMap.bilinearComp_apply] using
      (G.metric p.1).pullbackCoefficients_eq_of_comp_germ
        (he.mdifferentiableAt (by simp)) hkx heq' v w






theorem retainedPullbackCoefficients_smooth
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (hbirth : G.metric T = metric T)
    {V : Set E} (hV : IsOpen V) {A : E → (slice event.tMinus).carrier}
    (hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V)
    (hret : MapsTo A V (interior event.retained_pre)) :
    ContDiffOn ℝ ∞ (retainedPullbackCoefficients event G A) (Ioo event.tMinus b ×ˢ V) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  obtain ⟨U, W, hU, hW, hxW, _, hchart, hinside, k, hk, hmap, hfactor⟩ :=
    Poincare.exists_smooth_local_chart_factorization hV isOpen_interior hA hret hx
  have hs := retainedPullbackCoefficients_smooth_of_factorization event G hTb hbirth
    (A x) (hret hx) hU hW hchart hinside hk hmap hfactor
  exact (hs.contDiffAt ((isOpen_Ioo.prod hW).mem_nhds ⟨ht, hxW⟩)).contDiffWithinAt

end PoincareConjecture.M44
