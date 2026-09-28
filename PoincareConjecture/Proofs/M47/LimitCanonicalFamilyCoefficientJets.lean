import PoincareConjecture.Proofs.M47.LimitCanonicalRoundCoefficientJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E₃ →L[ℝ] E₃ →L[ℝ] ℝ

noncomputable local instance : NormedAddCommGroup (E₃ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ (E₃ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E₃ G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_eventually_family_bilinear_jets
    (P : M47Predecessors.{u}) (q : G.limit.sliceCarrier.carrier) (m : ℕ)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ J)
    {H : Set E₃} (hH : IsCompact H) (hHt : H ⊆ (extChartAt (𝓡 3) q).target)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ k in atTop,
      Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧
      (extChartAt (𝓡 3) q).symm '' H ⊆ G.exhaustion.space k ∧
      ∀ s ∈ Ktime, ∀ x ∈ H,
        ContDiffAt ℝ ∞ (blowupCoordinateBilinear (G.embedding k) q s) x ∧
        ContDiffAt ℝ ∞ (limitCoordinateBilinear G.limit q s) x ∧
        ‖iteratedFDeriv ℝ m (blowupCoordinateBilinear (G.embedding k) q s) x -
          iteratedFDeriv ℝ m (limitCoordinateBilinear G.limit q s) x‖ < rho := by
  let c := extChartAt (𝓡 3) q
  let L : (Fin 3 → Fin 3 → ℝ) →L[ℝ] Bilin :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  obtain ⟨C, hC, hbound⟩ := exists_piLpBilinearFromCoordinates_jet_bound
    (p := 2) (q := 2) (𝕜 := ℝ) (I := Fin 3) (J := Fin 3) (F := ℝ) (E := E₃)
  let eta := rho / (C + 1)
  have heta : 0 < eta := div_pos hrho (by positivity)
  have hsmall : C * eta < rho := by
    have hh : (C + 1) * eta = rho := by dsimp only [eta]; field_simp
    nlinarith
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex G.limit.flow.interval.convex
    (G.limit.flow.interval.convex.nontrivial_iff_nonempty_interior.mp G.limit.flow.nontrivial)
  filter_upwards [limitNoncollapse_generalized_compact_spatial_jets P G hJ q m
    hKtime hKJ hH hHt heta] with k hk
  refine ⟨hk.1, hk.2.1, ?_⟩
  intro s hs x hx
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space k, G.exhaustion.space_open k⟩
  let W := c.target ∩ c.symm ⁻¹' (U : Set G.limit.sliceCarrier.carrier)
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) U.isOpen
  have hxW : x ∈ W := ⟨hHt hx, hk.2.1 (mem_image_of_mem c.symm hx)⟩
  let f : E₃ → Fin 3 → Fin 3 → ℝ := fun y a b =>
    blowupPullbackCoefficient (G.embedding k) q a b (s, y)
  let g : E₃ → Fin 3 → Fin 3 → ℝ := fun y a b =>
    FlowCarrier.coordinateCoefficient G.limit.carrier q
      (fun t z v w => (G.limit.flow.metric t).inner z v w) a b (s, y)
  have hf (a b : Fin 3) : ContDiffAt ℝ ∞ (fun y => f y a b) x := by
    have hreg := limitNoncollapse_generalized_coefficient_contDiffOn P
      (G.exhaustion.time_pos k) U ⟨G.limit.base, G.exhaustion.base_mem k⟩
      (G.embedding k) q a b
    have hslice : ContDiffOn ℝ ∞ (fun y => f y a b) W :=
      hreg.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hk.1 hs, hy⟩)
    exact hslice.contDiffAt (hW.mem_nhds hxW)
  have hg (a b : Fin 3) : ContDiffAt ℝ ∞ (fun y => g y a b) x := by
    have hslice : ContDiffOn ℝ ∞ (fun y => g y a b) c.target :=
      (G.limit.flow.contDiffOn_chartMetric q a b).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hKJ hs, hy⟩)
    exact hslice.contDiffAt ((isOpen_extChartAt_target q).mem_nhds (hHt hx))
  have hBf := ContDiffAt.piLpBilinearFromCoordinates (p := 2) (q := 2) hf
  have hBg := ContDiffAt.piLpBilinearFromCoordinates (p := 2) (q := 2) hg
  refine ⟨hBf, hBg, ?_⟩
  have hfm (a b : Fin 3) : ContDiffAt ℝ m (fun y => f y a b) x :=
    (hf a b).of_le (by exact_mod_cast le_top)
  have hgm (a b : Fin 3) : ContDiffAt ℝ m (fun y => g y a b) x :=
    (hg a b).of_le (by exact_mod_cast le_top)
  have hb := hbound m (fun y a b => f y a b - g y a b) x
    (fun a b => (hfm a b).sub (hgm a b)) eta (fun a b => by
      change ‖iteratedFDeriv ℝ m ((fun y => f y a b) - (fun y => g y a b)) x‖ ≤ eta
      rw [iteratedFDeriv_sub_apply (hfm a b) (hgm a b)]
      exact (hk.2.2 s hs x hx a b).le)
  have heq : (fun y => L (f y) - L (g y)) =
      (fun y => L (fun a b => f y a b - g y a b)) := by
    funext y
    exact (L.map_sub (f y) (g y)).symm
  change ‖iteratedFDeriv ℝ m (fun y => L (f y)) x -
    iteratedFDeriv ℝ m (fun y => L (g y)) x‖ < rho
  rw [← fun_iteratedFDeriv_sub_apply (hBf.of_le (by exact_mod_cast le_top))
    (hBg.of_le (by exact_mod_cast le_top)), heq]
  exact hb.trans_lt hsmall

end PoincareConjecture.M47
