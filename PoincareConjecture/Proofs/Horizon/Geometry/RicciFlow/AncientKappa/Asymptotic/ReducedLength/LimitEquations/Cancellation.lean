import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.GlobalPairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.HeatCutoffs
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.CompactCutoff


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

open RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem limitReducedLength_weakPairing_eq_zero_on_slab
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    {φ : G.limit.carrier.carrier × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ univ ×ˢ Ioo α β) :
    weakPairing G.limit.flow (fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) φ = 0 := by
  let u := fun z : G.limit.carrier.carrier × ℝ =>
    z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)
  have hu : ContinuousOn u (univ ×ˢ Icc α β) :=
    (G.reducedLengthPullback_limitDensity_continuousOn P strictMono_id l hlim).mono
      (fun z hz => ⟨mem_univ _, hα.trans_le hz.2.1⟩)
  have ht : ∀ τ ∈ Icc α β, -τ ∈ interior (Iio (0 : ℝ)) := by
    intro τ hτ
    rw [interior_Iio]
    exact neg_neg_of_pos (hα.trans_le hτ.1)
  let T := weakPairingLinearOfContinuousOn G.limit.flow ht hu
  let Φ : testFunctions (n := n)
      ((univ : Set G.limit.carrier.carrier) ×ˢ Ioo α β) := ⟨φ, hφ, hφc, hφs⟩
  have hT : ∀ ψ : testFunctions (n := n)
      ((univ : Set G.limit.carrier.carrier) ×ˢ Ioo α β),
      (∀ z, 0 ≤ ψ z) → 0 ≤ T ψ := by
    intro ψ hψ
    exact G.limitReducedLength_weakPairing_nonneg P strictMono_id l hlim hα
      ψ.property.1 ψ.property.2.1 ψ.property.2.2 hψ
  obtain ⟨χ, hχ, hexK, hχlim⟩ :=
    G.exists_limitDensity_vanishing_heat_cutoffs P hl hl0 hlim hα hαβ
  let A := Prod.snd '' tsupport φ
  have hA : IsCompact A := hφc.isCompact.image continuous_snd
  have hAI : A ⊆ Ioo α β := by
    rintro τ ⟨z, hz, rfl⟩
    exact (hφs hz).2
  obtain ⟨η, hη, hηc, hηs, hηrange, hηone, _⟩ :=
    Poincare.Manifold.exists_compact_smooth_cutoff 𝓘(ℝ, ℝ) hA isOpen_Ioo hAI
  let Ψ := fun j => productTest (hχ j).1 (hχ j).2.1 hη.contDiff hηc hηs
  have hΨ : ∀ j z, 0 ≤ Ψ j z := by
    intro j z
    exact mul_nonneg ((hχ j).2.2 z.1).1 (hηrange z.2).1
  have hone : ∀ᶠ j in atTop, ∀ z ∈ tsupport (Φ : G.limit.carrier.carrier × ℝ → ℝ),
      Ψ j z = 1 := by
    filter_upwards [hexK (Prod.fst '' tsupport φ) (hφc.isCompact.image continuous_fst)] with j hj
    intro z hz
    change χ j z.1 * η z.2 = 1
    rw [hj z.1 (mem_image_of_mem Prod.fst hz),
      hηone.self_of_nhdsSet z.2 (mem_image_of_mem Prod.snd hz), one_mul]
  exact apply_eq_zero_of_test_cutoffs T hT Φ Ψ hΨ hone
    (hχlim η hη.contDiff hηc hηs)



theorem limitReducedLength_weakPairing_eq_zero
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {φ : G.limit.carrier.carrier × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ univ ×ˢ Ioi (0 : ℝ)) :
    weakPairing G.limit.flow (fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) φ = 0 := by
  obtain ⟨a, ha, hlow⟩ := hφc.isCompact.exists_forall_le'
    continuous_snd.continuousOn (fun z hz => (hφs hz).2)
  obtain ⟨B, hB⟩ := hφc.isCompact.bddAbove_image continuous_snd.continuousOn
  apply G.limitReducedLength_weakPairing_eq_zero_on_slab P hl hl0 hlim
    (α := a / 2) (β := max B a + 1) (half_pos ha)
    (by have := le_max_right B a; linarith) hφ hφc
  intro z hz
  have hzl : a ≤ z.2 := hlow z hz
  have hzu : z.2 ≤ B := hB (mem_image_of_mem Prod.snd hz)
  exact ⟨mem_univ _, by linarith, by have := le_max_left B a; linarith⟩

end PoincareConjecture.AncientCompactTimeConvergence
