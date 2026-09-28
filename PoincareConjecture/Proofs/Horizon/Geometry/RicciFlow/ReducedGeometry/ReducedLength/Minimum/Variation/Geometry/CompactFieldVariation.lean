import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartPerturbationVelocity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u v

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_family_of_compact_linear_field
    (α : ℝ → M) (Y : ∀ s, P →L[ℝ] TangentSpace (𝓡 n) (α s))
    (U K : Set ℝ) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hY : ∀ z : P, ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, Y s z⟩ : TangentBundle (𝓡 n) M)) U) :
    ∃ (f : ℝ × P → M) (Ω : Set (ℝ × P)) (N : Set P),
      IsOpen Ω ∧ IsOpen N ∧ (0 : P) ∈ N ∧ K ×ˢ N ⊆ Ω ∧
        ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞ f Ω ∧
        (∀ s, f (s, 0) = α s) ∧
        (∀ s, Y s = 0 → ∀ z, f (s, z) = α s) ∧
        ∀ s ∈ K, ∀ z : P,
          (curveVelocity (n := n) (fun u : ℝ ↦ f (s, u • z)) 0 : E) = Y s z := by
  classical
  let W : ℝ → Set ℝ := fun t ↦ U ∩ α ⁻¹' (chartAt E (α t)).source
  have hW (t : ℝ) : IsOpen (W t) :=
    hα.continuousOn.isOpen_inter_preimage hU (chartAt E (α t)).open_source
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover W (fun t ht ↦
    (hW t).mem_nhds ⟨hKU ht, mem_chart_source E (α t)⟩)
  have hcover' : K ⊆ ⋃ i : S, W i := by
    intro s hs
    obtain ⟨t, htS, ht⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact Set.mem_iUnion.mpr ⟨⟨t, htS⟩, ht⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ))
    hK.isClosed (fun i : S ↦ W i) (fun i ↦ hW i) hcover'
  let B : S → ℝ → P →L[ℝ] E := fun i s ↦
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E (α i)) (α s)).comp (Y s)
  have hB (i : S) : ContDiffOn ℝ ∞ (B i) (W i) := by
    apply contDiffOn_clm_apply.mpr
    intro z
    have h := (tangentChartPhase_contMDiffOn (α i)).comp
      ((hY z).mono (show W i ⊆ U from Set.inter_subset_left)) (fun s hs ↦ hs.2)
    exact h.contDiffOn.snd
  have hpiece (i : S) (s : ℝ) (z : P) :
      chartVectorField (α i) (ρ i s • B i s z) (α s) = ρ i s • Y s z := by
    by_cases hz : ρ i s = 0
    · simp only [hz, zero_smul, chartVectorField, VectorField.mpullback, map_zero]
    · have hsi := hρ i (subset_tsupport (ρ i) (Function.mem_support.mpr hz))
      change (mfderiv (𝓡 n) (𝓡 n) (chartAt E (α i)) (α s)).inverse
        (ρ i s • mfderiv (𝓡 n) (𝓡 n) (chartAt E (α i)) (α s) (Y s z)) = _
      rw [map_smul]
      exact congrArg (fun v : TangentSpace (𝓡 n) (α s) ↦ ρ i s • v)
        (chartVectorField_differential (α i) (α s) (Y s z) hsi.2)
  have hfinite (L : Finset S) :
      ∃ (f : ℝ × P → M) (Ω : Set (ℝ × P)), IsOpen Ω ∧
        (∀ s ∈ K, (s, (0 : P)) ∈ Ω) ∧
        ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞ f Ω ∧
        (∀ s, f (s, 0) = α s) ∧
        (∀ s, Y s = 0 → ∀ z, f (s, z) = α s) ∧
        ∀ s ∈ K, ∀ z : P,
          (curveVelocity (n := n) (fun u : ℝ ↦ f (s, u • z)) 0 : E) =
            ∑ i ∈ L, ρ i s • Y s z := by
    induction L using Finset.induction_on with
    | empty =>
      refine ⟨fun z ↦ α z.1, U ×ˢ Set.univ, hU.prod isOpen_univ,
        fun s hs ↦ ⟨hKU hs, Set.mem_univ _⟩, ?_, fun _ ↦ rfl,
        fun _ _ _ ↦ rfl, ?_⟩
      · exact hα.comp contDiff_fst.contMDiff.contMDiffOn (fun z hz ↦ hz.1)
      · intro s hs z
        simp only [Finset.sum_empty, curveVelocity, mfderiv_const, zero_apply]
    | @insert i L hi ih =>
      obtain ⟨f, Ω, hΩ, hKΩ, hf, hcenter, hfixed, hvelocity⟩ := ih
      have hchart : ∀ s ∈ K ∩ tsupport (ρ i),
          f (s, 0) ∈ (chartAt E (α i)).source := by
        intro s hs
        rw [hcenter]
        exact (hρ i hs.2).2
      obtain ⟨V, hV, _, hKV, hg⟩ := weightedChartPerturbation_smooth_near_center
        (α i) (W i) (hW i) (ρ i) (ρ i).contMDiff.contDiff (hρ i)
        (B i) (hB i) f Ω hΩ hf K hKΩ hchart
      let g := weightedChartPerturbation (α i) (W i) (ρ i) (B i) f
      refine ⟨g, V, hV, hKV, hg, ?_, ?_, ?_⟩
      · intro s
        exact (weightedChartPerturbation_center (α i) (W i) (ρ i) (B i) f s).trans
          (hcenter s)
      · intro s hYs z
        have hBzero : B i s z = 0 := by
          change mfderiv (𝓡 n) (𝓡 n) (chartAt E (α i)) (α s) (Y s z) = 0
          rw [hYs]
          exact (mfderiv (𝓡 n) (𝓡 n) (chartAt E (α i)) (α s)).map_zero
        exact (weightedChartPerturbation_eq_of_zero (α i) (W i) (ρ i) (B i) f
          (s, z) (Or.inr hBzero)).trans (hfixed s hYs z)
      · intro s hs z
        have hbranch : ρ i s ≠ 0 → s ∈ W i ∧ f (s, 0) ∈ (chartAt E (α i)).source := by
          intro hne
          have hsi := hρ i (subset_tsupport (ρ i) (Function.mem_support.mpr hne))
          exact ⟨hsi, by rw [hcenter]; exact hsi.2⟩
        have hd := weightedChartPerturbation_curveVelocity (α i) (W i) (ρ i) (B i) f s z
          ((hf.contMDiffAt (hΩ.mem_nhds (hKΩ s hs))).mdifferentiableAt (by simp)) hbranch
        change curveVelocity (n := n) (fun u : ℝ ↦ g (s, u • z)) 0 = _ at hd
        rw [hvelocity s hs z, hcenter, hpiece] at hd
        rw [hd, Finset.sum_insert hi]
        exact add_comm _ _
  obtain ⟨f, Ω, hΩ, hKΩ, hf, hcenter, hfixed, hvelocity⟩ := hfinite Finset.univ
  have hnear : ∀ᶠ z : P in 𝓝 0, ∀ s ∈ K, (s, z) ∈ Ω := by
    apply hK.eventually_forall_of_forall_eventually
    intro s hs
    exact (hΩ.preimage (continuous_swap (X := P) (Y := ℝ))).mem_nhds (hKΩ s hs)
  obtain ⟨N, hNsub, hN, h0N⟩ := mem_nhds_iff.mp hnear
  refine ⟨f, Ω, N, hΩ, hN, h0N, fun z hz ↦ hNsub hz.2 z.1 hz.1,
    hf, hcenter, hfixed, ?_⟩
  intro s hs z
  have hsum : ∑ i : S, ρ i s = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hs
  calc
    _ = ∑ i : S, ρ i s • Y s z := hvelocity s hs z
    _ = (∑ i : S, ρ i s) • Y s z := Finset.sum_smul.symm
    _ = Y s z := by rw [hsum, one_smul]

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
