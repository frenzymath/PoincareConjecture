import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.Set.UnionLift

noncomputable section

open Set MeasureTheory Topology
open scoped ContDiff

namespace Poincare.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [μ.IsOpenPosMeasure]

theorem eqOn_inter_of_ae_eq {s t : Set E} (hs : IsOpen s) (ht : IsOpen t)
    {f g u : E → ℝ} (hf : ContinuousOn f s) (hg : ContinuousOn g t)
    (hfu : f =ᵐ[μ.restrict s] u) (hgu : g =ᵐ[μ.restrict t] u) :
    EqOn f g (s ∩ t) := by
  apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := μ) _ (hs.inter ht)
    (hf.mono inter_subset_left) (hg.mono inter_subset_right)
  have hf' : f =ᵐ[μ.restrict (s ∩ t)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hfu
  have hg' : g =ᵐ[μ.restrict (s ∩ t)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hgu
  exact hf'.trans hg'.symm

theorem exists_smooth_representative_of_local {O : Set E} {u : E → ℝ}
    (hlocal : ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      ∃ f : E → ℝ, ContDiffOn ℝ ∞ f V ∧ f =ᵐ[μ.restrict V] u) :
    ∃ U : E → ℝ, ContDiffOn ℝ ∞ U O ∧ U =ᵐ[μ.restrict O] u := by
  classical
  choose V hV hxV hVO f hf hfu using fun x : O => hlocal x x.property
  have hcover : O ⊆ ⋃ x : O, V x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hagree : ∀ (x y : O) (z : E), z ∈ V x → z ∈ V y → f x z = f y z := by
    intro x y z hzx hzy
    exact eqOn_inter_of_ae_eq (hV x) (hV y) (hf x).continuousOn
      (hf y).continuousOn (hfu x) (hfu y) ⟨hzx, hzy⟩
  let g : O → ℝ := Set.iUnionLift V (fun x z => f x z)
    (fun x y z hzx hzy => hagree x y z hzx hzy) O hcover
  let U : E → ℝ := fun x => if hx : x ∈ O then g ⟨x, hx⟩ else 0
  have hU : ∀ x : O, EqOn U (f x) (V x) := by
    intro x z hz
    have hzO : z ∈ O := hVO x hz
    have hglue : g ⟨z, hzO⟩ = f x z := Set.iUnionLift_of_mem
      (S := V) (T := O) ⟨z, hzO⟩ hz
    simpa only [U, dif_pos hzO] using hglue
  refine ⟨U, ?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro x hx
    refine ⟨V ⟨x, hx⟩, hV ⟨x, hx⟩, hxV ⟨x, hx⟩, ?_⟩
    exact ((hf ⟨x, hx⟩).mono inter_subset_right).congr
      (fun y hy => hU ⟨x, hx⟩ hy.2)
  · obtain ⟨T, hT, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
    have hOcover : O ⊆ ⋃ x ∈ T, V x := by rwa [hTcover]
    have hlocal_ae : ∀ x ∈ T, U =ᵐ[μ.restrict (V x)] u := by
      intro x _
      apply Filter.EventuallyEq.trans _ (hfu x)
      exact (ae_restrict_iff' (hV x).measurableSet).mpr
        (Filter.Eventually.of_forall fun z hz => hU x hz)
    exact ae_restrict_of_ae_restrict_of_subset hOcover
      ((ae_eq_restrict_biUnion_iff V hT U u).mpr hlocal_ae)

end Poincare.Analysis.Elliptic
