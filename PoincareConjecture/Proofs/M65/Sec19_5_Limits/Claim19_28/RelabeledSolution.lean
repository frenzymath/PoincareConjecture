import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingIntrinsic








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}




theorem m65ContinuousOn_smul_field {gamma : ℝ × ℝ → M}
    {Y : ∀ z, TangentSpace (𝓡 n) (gamma z)} {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hY : ContinuousOn (fun z => (⟨gamma z, Y z⟩ : TangentBundle (𝓡 n) M)) S)
    (hf : ContinuousOn f S) :
    ContinuousOn (fun z => (⟨gamma z, f z • Y z⟩ : TangentBundle (𝓡 n) M)) S := by
  intro z hz
  have hYz := hY z hz
  rw [FiberBundle.continuousWithinAt_totalSpace] at hYz ⊢
  refine ⟨hYz.1, ?_⟩
  have hscalar := (hf z hz).smul hYz.2
  apply hscalar.congr_of_eventuallyEq_of_mem _ hz
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (gamma z)
  have hnear : ∀ᶠ w in 𝓝[S] z, gamma w ∈ e.baseSet :=
    hYz.1 (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (gamma z)))
  filter_upwards [hnear] with w hw
  change (e ⟨gamma w, f w • Y w⟩).2 = f w • (e ⟨gamma w, Y w⟩).2
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hw,
    ← e.continuousLinearMapAt_apply_of_mem ℝ hw, map_smul]




theorem m65ShrinkingCurve_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hpos : ∀ x, 0 < deriv phi x)
    (hperiod : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) :
    M62ShrinkingCurve F (fun y t => c (phi y) t) := by
  have hdiff : Differentiable ℝ phi := hphi.differentiable (by simp)
  let relabel : ℝ × ℝ → ℝ × ℝ := fun z => (phi z.1, z.2)
  have hrel : ContDiff ℝ ∞ relabel := (hphi.comp contDiff_fst).prodMk contDiff_snd
  have hmap (J : Set ℝ) : MapsTo relabel (univ ×ˢ J) (univ ×ˢ J) :=
    fun z hz => ⟨mem_univ _, hz.2⟩
  have hvelocity (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      curveVelocity (n := n) (fun y => c (phi y) t) x =
        deriv phi x • curveVelocity (n := n) (fun y => c y t) (phi x) :=
    m65CurveVelocity_comp ((hc.spatial_regular t ht (phi x)).mdifferentiableAt (by norm_num))
      (hdiff x).hasDerivAt
  have hvcont := hc.velocity_continuous.comp hrel.continuous.continuousOn (hmap (Icc a b))
  have hscaled := m65ContinuousOn_smul_field hvcont
    (((hphi.continuous_deriv (by simp)).comp continuous_fst).continuousOn)
  refine {
    periodic := ?_
    spatial_regular := ?_
    joint_smooth := hc.joint_smooth.comp hrel.contMDiff.contMDiffOn (hmap (Ioo a b))
    immersed := ?_
    continuous := hc.continuous.comp hrel.continuous.continuousOn (hmap (Icc a b))
    velocity_continuous := ?_
    curvature_continuous := ?_
    equation := ?_
  }
  · intro t ht x
    rw [hperiod, hc.periodic t ht]
  · intro t ht
    have hphi2 : ContDiff ℝ 2 phi :=
      hphi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact (hc.spatial_regular t ht).comp hphi2.contMDiff
  · intro t ht x
    rw [hvelocity t ht x]
    exact smul_ne_zero (hpos x).ne' (hc.immersed t ht (phi x))
  · apply hscaled.congr
    intro z hz
    rw [TotalSpace.mk_inj]
    exact hvelocity z.2 hz.2 z.1
  · apply (hc.curvature_continuous.comp hrel.continuous.continuousOn (hmap (Icc a b))).congr
    intro z hz
    dsimp only [Function.comp_apply, relabel]
    rw [TotalSpace.mk_inj]
    exact m65CurvatureVector_fixed_relabeling c hc hdiff hpos hz.2 z.1
  · intro t ht x
    exact m65ShrinkingEquation_fixed_relabeling c hc hdiff hpos ht x




theorem m65ShrinkingCurve_exists_constantSpeed_solution (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {s : ℝ} (hs : s ∈ Ioo a b) :
    ∃ phi : ℝ ≃o ℝ, phi 0 = 0 ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      ContDiff ℝ ∞ (phi : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (phi : ℝ → ℝ) x) ∧
      M62ShrinkingCurve F (fun y t => c (phi y) t) ∧
      (∀ x, curveSpeed F (fun y t => c (phi y) t) s x =
        m62Length F c s / curvePeriod) := by
  obtain ⟨phi, hzero, hperiod, hphi, hpos, hspeed⟩ :=
    m65ShrinkingCurve_exists_constantSpeed_relabeling c hc hs
  refine ⟨phi, hzero, hperiod, hphi, hpos, ?_, ?_⟩
  · exact m65ShrinkingCurve_fixed_relabeling c hc hphi hpos hperiod
  · exact hspeed

end PoincareConjecture
