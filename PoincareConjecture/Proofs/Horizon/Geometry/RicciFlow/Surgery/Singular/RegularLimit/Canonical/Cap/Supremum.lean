import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit


theorem abs_sub_scalar_sup_le {X : Type*} [Nonempty X] (f g : X → ℝ)
    (hg : BddAbove (range g)) (ε : ℝ) (hfg : ∀ x, |f x - g x| ≤ ε) :
    |sSup (range f) - sSup (range g)| ≤ ε := by
  have hfg' (x : X) : f x ≤ g x + ε := by
    have := (abs_sub_le_iff.mp (hfg x)).1
    linarith
  have hgf' (x : X) : g x ≤ f x + ε := by
    have := (abs_sub_le_iff.mp (hfg x)).2
    linarith
  have hf : BddAbove (range f) := by
    refine ⟨sSup (range g) + ε, ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [hfg' x, le_csSup hg (mem_range_self x)]
  have hsupf : sSup (range f) ≤ sSup (range g) + ε := by
    apply csSup_le (range_nonempty f)
    rintro _ ⟨x, rfl⟩
    linarith [hfg' x, le_csSup hg (mem_range_self x)]
  have hsupg : sSup (range g) ≤ sSup (range f) + ε := by
    apply csSup_le (range_nonempty g)
    rintro _ ⟨x, rfl⟩
    linarith [hgf' x, le_csSup hf (mem_range_self x)]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem eventually_scalar_suprema_close_on_subsets
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[<] T, ∀ S : Set (H.regularRegion P04), S.Nonempty → S ⊆ A →
      |sSup (range (fun x : S => H.reference.scalar t (x : H.regularRegion P04))) -
        scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S| < ε := by
  have hcont := (P04.tensor_calculus 3 (H.regularRegion P04) (H.terminalMetric P04)
    (H.terminalConnection P04)).contMDiff_scalarCurvature.continuous
  have hbounded := (hA.image hcont).bddAbove
  have huniform := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) (ε / 2) (by positivity)
  filter_upwards [huniform] with t ht
  intro S hS hSA
  let _ : Nonempty S := nonempty_subtype.mpr hS
  have hSbounded : BddAbove (range (fun x : S =>
      (H.terminalConnection P04).scalarCurvature (x : H.regularRegion P04))) := by
    apply hbounded.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, hSA x.property, rfl⟩
  have h := SingularRegularLimit.abs_sub_scalar_sup_le
    (fun x : S => H.reference.scalar t (x : H.regularRegion P04))
    (fun x : S => (H.terminalConnection P04).scalarCurvature (x : H.regularRegion P04))
    hSbounded (ε / 2) (fun x => by
      simpa only [Real.dist_eq, abs_sub_comm] using (ht x (hSA x.property)).le)
  exact h.trans_lt (by linarith)



theorem tendsto_scalar_sup_on_captured_subset
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A S : Set (H.regularRegion P04)} (hA : IsCompact A) (hS : S.Nonempty) (hSA : S ⊆ A) :
    Tendsto (fun t => sSup (range (fun x : S => H.reference.scalar t
      (x : H.regularRegion P04)))) (𝓝[<] T)
      (𝓝 (scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [H.eventually_scalar_suprema_close_on_subsets P04 hA hε] with t ht
  simpa only [Real.dist_eq] using ht S hS hSA

end PoincareConjecture.SingularTimeAssumptions
