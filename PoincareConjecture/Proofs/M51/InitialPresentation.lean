import PoincareConjecture.Proofs.M51.InitialRawFlow








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51Initial

theorem admissible_of_no_events (F : SurgeryFlowData.{u}) (hS : F.surgery_times = ∅) :
    SurgeryFlowAdmissible F where
  strong_boundaries := by intro T hT; simp only [hS, mem_empty_iff_false] at hT
  strong_disappearing := by intro T hT; simp only [hS, mem_empty_iff_false] at hT
  strong_vanishing := by intro T hT; simp only [hS, mem_empty_iff_false] at hT

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
  (g0 : StandardInitialMetric) (K : MetricSurgeryConstants) (P : SurgeryParameters)
  (I : NormalizedInitialMetric (M := M))
  (hRP : NoTrivialNormalProjectivePlane (M := M))
  {J : Set ℝ} (F : RicciFlow 3 M J) (h0 : F.metric 0 = I.metric)
  (hleast : IsLeast J 0)
  (hmax : ∀ b : ℝ, 0 < b → Ico 0 b ⊆ J → b ∉ J →
    ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max 0 s) b, ∃ x : M,
      L < (F.connection t).curvatureTensorNorm x)

noncomputable def preterminal (T : ℝ) (hT : 0 < T) (hJ : J = Ico 0 T) :
    RepairedPreterminalSlab (rawFlow g0 K P I hRP F h0 hleast hmax) T where
  start := 0
  start_mem := hleast.1
  start_lt := hT
  start_initial_or_surgery := Or.inl rfl
  time_subset := hJ ▸ Subset.rfl
  surgery_free := by simp [rawFlow]
  flow := M51Ordinary.restrict F (hJ ▸ Subset.rfl) ordConnected_Ico (by
    refine ⟨0, ⟨le_rfl, hT⟩, T / 2, ⟨by linarith, by linarith⟩, ?_⟩
    linarith)
  identify := fun _ => Diffeomorph.refl (𝓡 3) M ∞
  initial_identify := fun _ => rfl
  metric_pullback := by
    intro t x v w
    dsimp only [rawFlow] at x v w ⊢
    change (F.metric t.1).inner (id x)
      (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x w) = _
    simp only [mfderiv_id]
    rfl
  transport_compatibility := by intros; rfl
  curvature_unbounded := hmax T hT (hJ ▸ Subset.rfl) (by simp [hJ])

@[simp] theorem preterminal_start (T : ℝ) (hT : 0 < T) (hJ : J = Ico 0 T) :
    (preterminal g0 K P I hRP F h0 hleast hmax T hT hJ).start = 0 := rfl

end PoincareConjecture.M51Initial
