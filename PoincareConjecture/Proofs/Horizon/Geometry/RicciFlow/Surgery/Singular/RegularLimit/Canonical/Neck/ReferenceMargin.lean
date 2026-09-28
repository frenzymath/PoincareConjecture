import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.BoxMargin

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

theorem exists_reference_neck_scalar_time_derivative_margin
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) {t ε : ℝ}
        (ht : t ∈ Ioo H.reference.tMinus T) (N : GeneralizedStrongNeck F t ε),
        ε ≤ ε₀ → ∀ x : M,
          N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x →
          ∃ d : ℝ, HasDerivAt (fun s => H.reference.scalar s x) d t ∧
            (1 / 2 : ℝ) * H.reference.scalar t x ^ 2 ≤ d := by
  obtain ⟨ε₀, hε₀, hsmall, hmargin⟩ :=
    GeneralizedStrongNeck.exists_box_scalar_time_derivative_margin P04
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H t ε ht N hε x hcenter
  have ht' : t ∈ Ico H.reference.tMinus T := ⟨ht.1.le, ht.2⟩
  obtain ⟨b, y, δ, hδ, hbox⟩ := H.reference.vertical_compatibility t ht' x
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo H.reference.tMinus T ∧ |s - t| < δ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2, Metric.ball_mem_nhds t hδ] with s hs hdist
    exact ⟨hs, by simpa only [Metric.mem_ball, Real.dist_eq] using hdist⟩
  have hmem : (F.box b).interval ∈ 𝓝 t := by
    filter_upwards [hnear] with s hs
    exact (hbox s ⟨hs.1.1.le, hs.1.2⟩ hs.2).choose
  have heq : (fun s => H.reference.scalar s x) =ᶠ[𝓝 t]
      (fun s => ((F.box b).flow.connection s).scalarCurvature y) := by
    filter_upwards [hnear] with s hs
    obtain ⟨hb, hforward⟩ := hbox s ⟨hs.1.1.le, hs.1.2⟩ hs.2
    dsimp only [SingularTimeReference.scalar]
    rw [← H.reference.scalar_pullback s ⟨hs.1.1.le, hs.1.2⟩ x,
      hforward, ← F.box_scalar b s hb y]
  obtain ⟨hb, hforward⟩ := hbox t ht' (by simpa only [sub_self, abs_zero] using hδ)
  obtain ⟨d, hd, hbound⟩ := hmargin N hε b hb y (hforward.symm.trans hcenter.symm)
  refine ⟨d, (hd.hasDerivAt hmem).congr_of_eventuallyEq heq, ?_⟩
  rw [hcenter, H.reference.scalar_pullback t ht' x] at hbound
  exact hbound

end PoincareConjecture.SingularRegularLimit
