import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem tendstoUniformlyOn_terminal_scalar_rpow
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (hpos : ∀ x ∈ A, 0 < (H.terminalConnection P04).scalarCurvature x) (p : ℝ) :
    TendstoUniformlyOn (fun t (x : H.regularRegion P04) => (H.reference.scalar t x) ^ p)
      (fun x => ((H.terminalConnection P04).scalarCurvature x) ^ p) (𝓝[<] T) A := by
  obtain ⟨a, ha, hlower⟩ := hA.exists_forall_le'
    (H.terminalConnection P04).continuous_scalarCurvature.continuousOn hpos
  let δ : ℝ := a / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let G := H.terminalFlow P04
  have hcontinuous : ContinuousOn
      (fun z : ℝ × H.regularRegion P04 =>
        (max δ ((G.connection z.1).scalarCurvature z.2)) ^ p)
      (Ioc H.reference.tMinus T ×ˢ A) := by
    apply (continuousOn_const.sup
      (G.contMDiffOn_scalarCurvature.continuousOn.mono
        (prod_mono subset_rfl (subset_univ A)))).rpow_const
    intro z hz
    exact Or.inl (hδ.trans_le (le_max_left _ _)).ne'
  have huniform : TendstoUniformlyOn
      (fun t (x : H.regularRegion P04) => (max δ ((G.connection t).scalarCurvature x)) ^ p)
      (fun x => (max δ ((G.connection T).scalarCurvature x)) ^ p)
      (𝓝[Ioc H.reference.tMinus T] T) A := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨V, hV, hbound⟩ := hA.mem_uniformity_of_prod
      (f := fun t x => (max δ ((G.connection t).scalarCurvature x)) ^ p)
      hcontinuous ⟨H.reference.tMinus_lt, le_rfl⟩ (Metric.dist_mem_uniformity hε)
    filter_upwards [hV] with t ht x hx
    have hb : dist ((max δ ((G.connection t).scalarCurvature x)) ^ p)
        ((max δ ((G.connection T).scalarCurvature x)) ^ p) < ε := hbound t ht x hx
    rwa [dist_comm] at hb
  have hfilter : 𝓝[<] T ≤ 𝓝[Ioc H.reference.tMinus T] T :=
    nhdsWithin_le_of_mem (Ioc_mem_nhdsLT H.reference.tMinus_lt)
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) δ hδ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hfilter (Metric.tendstoUniformlyOn_iff.mp huniform ε hε), hclose,
    self_mem_nhdsWithin] with t ht hclose htT x hx
  have hT : δ ≤ (G.connection T).scalarCurvature x := by
    rw [H.terminalFlow_scalar_at_terminal P04]
    exact (show δ ≤ a by dsimp [δ]; linarith).trans (hlower x hx)
  have ht' : δ ≤ (G.connection t).scalarCurvature x := by
    rw [H.terminalFlow_scalar_of_ne P04 htT.ne]
    have h := hclose x hx
    rw [Real.dist_eq] at h
    have h' := (abs_sub_lt_iff.mp h).1
    have hl := hlower x hx
    dsimp [δ] at hδ h' ⊢
    linarith
  have h := ht x hx
  rw [max_eq_right hT, max_eq_right ht', H.terminalFlow_scalar_at_terminal P04,
    H.terminalFlow_scalar_of_ne P04 htT.ne] at h
  exact h

end PoincareConjecture.SingularTimeAssumptions
