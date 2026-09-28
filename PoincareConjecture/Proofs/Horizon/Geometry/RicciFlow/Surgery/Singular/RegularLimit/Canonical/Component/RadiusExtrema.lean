import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.ScalarPowers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Supremum



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit


theorem abs_sub_scalar_inf_le {X : Type*} [Nonempty X] (f g : X → ℝ)
    (hg : BddBelow (range g)) (ε : ℝ) (hfg : ∀ x, |f x - g x| ≤ ε) :
    |sInf (range f) - sInf (range g)| ≤ ε := by
  have hfg' (x : X) : f x ≤ g x + ε := by
    have := (abs_sub_le_iff.mp (hfg x)).1
    linarith
  have hgf' (x : X) : g x ≤ f x + ε := by
    have := (abs_sub_le_iff.mp (hfg x)).2
    linarith
  have hf : BddBelow (range f) := by
    refine ⟨sInf (range g) - ε, ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [hgf' x, csInf_le hg (mem_range_self x)]
  have hfginf : sInf (range f) - ε ≤ sInf (range g) := by
    apply le_csInf (range_nonempty g)
    rintro _ ⟨x, rfl⟩
    linarith [hfg' x, csInf_le hf (mem_range_self x)]
  have hgfinf : sInf (range g) - ε ≤ sInf (range f) := by
    apply le_csInf (range_nonempty f)
    rintro _ ⟨x, rfl⟩
    linarith [hgf' x, csInf_le hg (mem_range_self x)]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem tendsto_terminal_scalarRadius_sup
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) (hne : A.Nonempty)
    (hpos : ∀ x ∈ A, 0 < (H.terminalConnection P04).scalarCurvature x) :
    Tendsto (fun t => sSup (range (fun x : A =>
      H.reference.scalar t (x : H.regularRegion P04) ^ (-1 / 2 : ℝ)))) (𝓝[<] T)
      (𝓝 (sSup (range (fun x : A =>
        (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))))) := by
  let _ : Nonempty A := nonempty_subtype.mpr hne
  have hcontinuous := (H.terminalConnection P04).continuous_scalarCurvature.continuousOn.rpow_const
    (p := (-1 / 2 : ℝ)) (fun x hx => Or.inl (hpos x hx).ne')
  have hbounded : BddAbove (range (fun x : A =>
      (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
    apply (hA.bddAbove_image hcontinuous).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalar_rpow P04 hA hpos (-1 / 2))
      (ε / 2) (by positivity)] with t ht
  have h := SingularRegularLimit.abs_sub_scalar_sup_le
    (fun x : A => H.reference.scalar t (x : H.regularRegion P04) ^ (-1 / 2 : ℝ))
    (fun x : A => (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))
    hbounded (ε / 2) (fun x => by
      simpa only [Real.dist_eq, abs_sub_comm] using (ht x x.property).le)
  exact (by simpa only [Real.dist_eq] using h.trans_lt (by linarith))

theorem tendsto_terminal_scalarRadius_inf
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) (hne : A.Nonempty)
    (hpos : ∀ x ∈ A, 0 < (H.terminalConnection P04).scalarCurvature x) :
    Tendsto (fun t => sInf (range (fun x : A =>
      H.reference.scalar t (x : H.regularRegion P04) ^ (-1 / 2 : ℝ)))) (𝓝[<] T)
      (𝓝 (sInf (range (fun x : A =>
        (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))))) := by
  let _ : Nonempty A := nonempty_subtype.mpr hne
  have hcontinuous := (H.terminalConnection P04).continuous_scalarCurvature.continuousOn.rpow_const
    (p := (-1 / 2 : ℝ)) (fun x hx => Or.inl (hpos x hx).ne')
  have hbounded : BddBelow (range (fun x : A =>
      (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
    apply (hA.bddBelow_image hcontinuous).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalar_rpow P04 hA hpos (-1 / 2))
      (ε / 2) (by positivity)] with t ht
  have h := SingularRegularLimit.abs_sub_scalar_inf_le
    (fun x : A => H.reference.scalar t (x : H.regularRegion P04) ^ (-1 / 2 : ℝ))
    (fun x : A => (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))
    hbounded (ε / 2) (fun x => by
      simpa only [Real.dist_eq, abs_sub_comm] using (ht x x.property).le)
  exact (by simpa only [Real.dist_eq] using h.trans_lt (by linarith))

theorem terminal_scalarRadius_extrema_pos
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) (hne : A.Nonempty)
    (hpos : ∀ x ∈ A, 0 < (H.terminalConnection P04).scalarCurvature x) :
    0 < sSup (range (fun x : A =>
      (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))) ∧
    0 < sInf (range (fun x : A =>
      (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
  let _ : Nonempty A := nonempty_subtype.mpr hne
  have hcontinuous := (H.terminalConnection P04).continuous_scalarCurvature.continuousOn.rpow_const
    (p := (-1 / 2 : ℝ)) (fun x hx => Or.inl (hpos x hx).ne')
  have hbounded : BddAbove (range (fun x : A =>
      (H.terminalConnection P04).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
    apply (hA.bddAbove_image hcontinuous).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  obtain ⟨a, ha, hbound⟩ := hA.exists_forall_le' hcontinuous
    (fun x hx => Real.rpow_pos_of_pos (hpos x hx) (-1 / 2))
  obtain ⟨x, hx⟩ := hne
  constructor
  · exact (Real.rpow_pos_of_pos (hpos x hx) (-1 / 2)).trans_le
      (le_csSup hbounded ⟨⟨x, hx⟩, rfl⟩)
  · apply ha.trans_le
    apply le_csInf (range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact hbound z z.property

end PoincareConjecture.SingularTimeAssumptions
