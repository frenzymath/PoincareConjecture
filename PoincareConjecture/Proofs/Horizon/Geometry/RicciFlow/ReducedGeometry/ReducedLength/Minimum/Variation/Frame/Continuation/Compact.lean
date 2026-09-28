import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Continuation.Maximal









set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_uniform_adaptedRestartRadius {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (C : Set ℝ) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ d : ℝ, 0 < d ∧ ∀ t ∈ C, ∀ v : TangentSpace (𝓡 n) (γ t),
      ∃ A : AdaptedIntervalSolution F T γ U t v,
        Ioo (t - d) (t + d) ⊆ A.domain := by
  classical
  choose W r hW hmem hWU hr hsol using fun t : C ↦
    exists_uniform_local_isAdaptedFieldOn F T γ U hU htime hγ t (hCU t.property)
  obtain ⟨S, hS⟩ := hC.elim_finite_subcover W hW
    (fun t ht ↦ mem_iUnion.mpr ⟨⟨t, ht⟩, hmem ⟨t, ht⟩⟩)
  have hbound (S : Finset C) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ S, d ≤ r i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S _ ih =>
      obtain ⟨d, hd, hdi⟩ := ih
      refine ⟨min d (r i), lt_min hd (hr i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hdi j hj)
  obtain ⟨d, hd, hdi⟩ := hbound S
  refine ⟨d, hd, ?_⟩
  intro t ht v
  obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp (hS ht)
  obtain ⟨P, hPU, hP₀, hP⟩ := hsol i t hti v
  let A : AdaptedIntervalSolution F T γ U t v := {
    domain := Ioo (t - r i) (t + r i)
    open_domain := isOpen_Ioo
    preconnected_domain := isPreconnected_Ioo
    initial_mem := ⟨by linarith [hr i], by linarith [hr i]⟩
    domain_subset := hPU
    field := P
    adapted := hP
    initial_value := hP₀ }
  refine ⟨A, ?_⟩
  intro s hs
  change t - r i < s ∧ s < t + r i
  have hle := hdi i hi
  constructor <;> linarith [hs.1, hs.2]

private theorem Icc_subset_of_uniform_open_intervals_at (D : Set ℝ) (hD : IsOpen D)
    (a c s₀ : ℝ) (hs₀ : s₀ ∈ Icc a c) (h₀ : s₀ ∈ D) (r : ℝ) (hr : 0 < r)
    (hstep : ∀ t ∈ Icc a c, t ∈ D → Ioo (t - r) (t + r) ⊆ D) :
    Icc a c ⊆ D := by
  let C := Icc a c
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let A : Set C := {t | (t : ℝ) ∈ D}
  have hopen : IsOpen A := hD.preimage continuous_subtype_val
  have hcompl : IsOpen Aᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hN : Ioo ((t : ℝ) - r) ((t : ℝ) + r) ∈ 𝓝 (t : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [continuousAt_subtype_val.preimage_mem_nhds hN] with z hz
    change (z : ℝ) ∉ D
    intro hzD
    apply ht
    exact hstep z z.property hzD ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hAll : A = univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hcompl, hopen⟩
    ⟨⟨s₀, hs₀⟩, h₀⟩
  intro s hs
  have hm : (⟨s, hs⟩ : C) ∈ A := by rw [hAll]; trivial
  exact hm

theorem exists_adaptedFieldOn_Icc {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (a c s₀ : ℝ) (hCU : Icc a c ⊆ U) (hs₀ : s₀ ∈ Icc a c)
    (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    ∃ (D : Set ℝ) (P : ∀ t, TangentSpace (𝓡 n) (γ t)),
      IsOpen D ∧ IsPreconnected D ∧ Icc a c ⊆ D ∧ D ⊆ U ∧
        P s₀ = v₀ ∧ IsAdaptedFieldOn F T γ P D := by
  let A := maximalAdaptedSolution F T γ U hU htime hγ s₀ (hCU hs₀) v₀
  obtain ⟨d, hd, hrestart⟩ := exists_uniform_adaptedRestartRadius F T γ U hU htime hγ
    (Icc a c) isCompact_Icc hCU
  have hcover : Icc a c ⊆ A.domain := by
    apply Icc_subset_of_uniform_open_intervals_at A.domain A.open_domain a c s₀ hs₀
      A.initial_mem d hd
    intro t ht htA
    obtain ⟨B, hB⟩ := hrestart t ht (A.field t)
    exact hB.trans (maximalAdaptedDomain_contains_restart F T γ U hU htime hγ
      s₀ (hCU hs₀) v₀ t htA B)
  exact ⟨A.domain, A.field, A.open_domain, A.preconnected_domain, hcover,
    A.domain_subset, A.initial_value, A.adapted⟩

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
