import PoincareConjecture.Proofs.M47.LimitNoncollapseIncludedJets
import PoincareConjecture.Proofs.M47.LimitNoncollapseCoefficients
import PoincareConjecture.Proofs.M34.Mathlib.NeckFiniteBilinearJets
import PoincareConjecture.Proofs.M34.Mathlib.NeckBilinearSmooth
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckBilinearReadout
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E3 →L[ℝ] E3 →L[ℝ] ℝ

noncomputable local instance : NormedAddCommGroup (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

private theorem reconstructed_convergence
    {f : ℕ → E3 → Fin 3 → Fin 3 → ℝ} {g : E3 → Fin 3 → Fin 3 → ℝ}
    {U : Set E3}
    (h : ∀ a b, CompactSmoothConvergenceOn (fun k x => f k x a b)
      (fun x => g x a b) atTop U) :
    CompactSmoothConvergenceOn
      (fun k x => ContinuousLinearMap.piLpBilinearFromCoordinates
        (p := 2) (q := 2) (𝕜 := ℝ) (f k x))
      (fun x => ContinuousLinearMap.piLpBilinearFromCoordinates
        (p := 2) (q := 2) (𝕜 := ℝ) (g x)) atTop U := by
  let L : (Fin 3 → Fin 3 → ℝ) →L[ℝ] Bilin :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  have hU := (h 0 0).isOpen
  have hg (x : E3) (hx : x ∈ U) :
      ∀ a b, ContDiffAt ℝ ∞ (fun y => g y a b) x :=
    fun a b => (h a b).smooth.contDiffAt (hU.mem_nhds hx)
  have hs (K : Set E3) (hK : IsCompact K) (hKU : K ⊆ U) :
      ∀ᶠ k in atTop, ∀ a b, ∀ x ∈ K,
        ContDiffAt ℝ ∞ (fun y => f k y a b) x := by
    simp only [eventually_all]
    exact fun a b => (h a b).eventually_smooth K hK hKU
  refine ⟨hU, ?_, ?_, ?_⟩
  · intro x hx
    exact (ContDiffAt.piLpBilinearFromCoordinates (hg x hx)).contDiffWithinAt
  · intro K hK hKU
    filter_upwards [hs K hK hKU] with k hk x hx
    exact ContDiffAt.piLpBilinearFromCoordinates (fun a b => hk a b x hx)
  · intro m K hK hKU
    obtain ⟨C, hC, hbound⟩ := exists_piLpBilinearFromCoordinates_jet_bound
      (p := 2) (q := 2) (𝕜 := ℝ) (I := Fin 3) (J := Fin 3)
      (F := ℝ) (E := EuclideanSpace ℝ (Fin 3))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro epsilon hepsilon
    let delta := epsilon / (C + 1)
    have hd : 0 < delta := div_pos hepsilon (by positivity)
    have hCd : C * delta < epsilon := by
      dsimp only [delta]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith
    have hj : ∀ᶠ k in atTop, ∀ a b, ∀ x ∈ K,
        dist (iteratedFDeriv ℝ m (fun y => g y a b) x)
          (iteratedFDeriv ℝ m (fun y => f k y a b) x) < delta := by
      simp only [eventually_all]
      exact fun a b => Metric.tendstoUniformlyOn_iff.mp ((h a b).jets m K hK hKU) delta hd
    filter_upwards [hs K hK hKU, hj] with k hk hkj x hx
    have hfk (a b : Fin 3) : ContDiffAt ℝ m (fun y => f k y a b) x :=
      (hk a b x hx).of_le (by exact_mod_cast le_top)
    have hgk (a b : Fin 3) : ContDiffAt ℝ m (fun y => g y a b) x :=
      (hg x (hKU hx) a b).of_le (by exact_mod_cast le_top)
    have hdiff : (fun y => L (f k y) - L (g y)) =
        (fun y => L (fun a b => f k y a b - g y a b)) := by
      funext y
      exact (L.map_sub (f k y) (g y)).symm
    have hb := hbound m (fun y a b => f k y a b - g y a b) x
      (fun a b => (hfk a b).sub (hgk a b)) delta (fun a b => by
        change ‖iteratedFDeriv ℝ m
          ((fun y => f k y a b) - (fun y => g y a b)) x‖ ≤ delta
        have he := iteratedFDeriv_sub_apply (hfk a b) (hgk a b)
        rw [he]
        simpa only [dist_eq_norm, norm_sub_rev] using (hkj a b x hx).le)
    change dist (iteratedFDeriv ℝ m (fun y => L (g y)) x)
      (iteratedFDeriv ℝ m (fun y => L (f k y)) x) < epsilon
    have he := iteratedFDeriv_sub_apply
      (ContDiffAt.piLpBilinearFromCoordinates (p := 2) (q := 2) hfk)
      (ContDiffAt.piLpBilinearFromCoordinates (p := 2) (q := 2) hgk)
    rw [dist_eq_norm, norm_sub_rev, ← he]
    change ‖iteratedFDeriv ℝ m (fun y => L (f k y) - L (g y)) x‖ < epsilon
    rw [hdiff]
    exact hb.trans_lt hCd

section ActualConvergence

variable (P : M47Predecessors.{u}) {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

include P

theorem limitCanonical_round_scalar_coefficient_convergence
    (q : G.limit.sliceCarrier.carrier) (t : ℝ) (ht : t ∈ J) (a b : Fin 3) :
    CompactSmoothConvergenceOn
      (fun k y => blowupPullbackCoefficient (G.embedding k) q a b (t, y))
      (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
        (fun s x v w => (G.limit.flow.metric s).inner x v w) a b (t, y))
      atTop (extChartAt (𝓡 3) q).target := by
  let c := extChartAt (𝓡 3) q
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex G.limit.flow.interval.convex
    (G.limit.flow.interval.convex.nontrivial_iff_nonempty_interior.mp G.limit.flow.nontrivial)
  have htJ : ({t} : Set ℝ) ⊆ J := singleton_subset_iff.mpr ht
  refine ⟨isOpen_extChartAt_target q, ?_, ?_, ?_⟩
  · exact (G.limit.flow.contDiffOn_chartMetric q a b).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨ht, hy⟩)
  · intro K hK hKt
    filter_upwards [limitNoncollapse_generalized_compact_spatial_jets P G hJ q 0
      isCompact_singleton htJ hK hKt (by norm_num : (0 : ℝ) < 1)] with k hk
    let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
      ⟨G.exhaustion.space k, G.exhaustion.space_open k⟩
    let W := c.target ∩ c.symm ⁻¹' (U : Set G.limit.sliceCarrier.carrier)
    have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) U.isOpen
    have hs : ContDiffOn ℝ ∞
        (fun y => blowupPullbackCoefficient (G.embedding k) q a b (t, y)) W :=
      (limitNoncollapse_generalized_coefficient_contDiffOn P (G.exhaustion.time_pos k)
        U ⟨G.limit.base, G.exhaustion.base_mem k⟩ (G.embedding k) q a b).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hk.1 (mem_singleton t), hy⟩)
    intro x hx
    exact hs.contDiffAt (hW.mem_nhds ⟨hKt hx, hk.2.1 (mem_image_of_mem c.symm hx)⟩)
  · intro m K hK hKt
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro epsilon hepsilon
    filter_upwards [limitNoncollapse_generalized_compact_spatial_jets P G hJ q m
      isCompact_singleton htJ hK hKt hepsilon] with k hk x hx
    simpa only [dist_eq_norm, norm_sub_rev] using hk.2.2 t (mem_singleton t) x hx a b

theorem limitCanonical_round_bilinear_coefficient_convergence
    (q : G.limit.sliceCarrier.carrier) (t : ℝ) (ht : t ∈ J) :
    CompactSmoothConvergenceOn
      (fun k y => ContinuousLinearMap.piLpBilinearFromCoordinates
        (p := 2) (q := 2) (𝕜 := ℝ)
        (fun a b : Fin 3 => blowupPullbackCoefficient (G.embedding k) q a b (t, y)))
      ((G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm)
      atTop (extChartAt (𝓡 3) q).target := by
  have h := reconstructed_convergence
    (fun a b => limitCanonical_round_scalar_coefficient_convergence P G q t ht a b)
  apply h.congr (fun _ _ _ => rfl)
  intro x _hx
  symm
  ext v w
  exact M34.limitCoordinateBilinear_apply (L := G.limit) q t x v w

end ActualConvergence

theorem limitCanonical_round_reconstructed_eq_chartForm
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin scale I U) (hU : IsOpen U)
    (q : L.sliceCarrier.carrier) (t : ℝ) (ht : t ∈ I) (x : E3)
    (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxu : (extChartAt (𝓡 3) q).symm x ∈ U) :
    ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
        (fun a b : Fin 3 => blowupPullbackCoefficient e q a b (t, x)) =
      limitNoncollapseChartForm e q t ht x := by
  have heq : (fun a b : Fin 3 => blowupPullbackCoefficient e q a b (t, x)) =
      (fun a b => limitNoncollapseChartForm e q t ht x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
    funext a b
    exact (limitNoncollapseChartForm_coefficient e hU q t ht x hx hxu a b).symm
  rw [heq]
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.single] using
    ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations
      (limitNoncollapseChartForm e q t ht x)

end PoincareConjecture.M47
