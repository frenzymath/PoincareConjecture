import PoincareConjecture.Proofs.M09.AdaptedRestartGluing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_uniform_adaptedRestartRadius {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (K : Set ℝ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d : ℝ, 0 < d ∧ ∀ t ∈ K, ∀ v : TangentSpace (𝓡 n) (γ t),
      ∃ A : AdaptedIntervalSolution F T γ U t v,
        Set.Ioo (t - d) (t + d) ⊆ A.domain := by
  classical
  choose W r hW hmem hWU hr hsol using fun t : K ↦
    exists_uniform_local_isAdaptedFieldOn F T b hb hwindow γ U hU htime hγ t (hKU t.property)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover W hW (fun t ht ↦
    Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hmem ⟨t, ht⟩⟩)
  have hbound (S : Finset K) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ S, d ≤ r i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨d, hd, hdi⟩ := ih
      refine ⟨min d (r i), lt_min hd (hr i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hdi j hj)
  obtain ⟨d, hd, hdi⟩ := hbound S
  refine ⟨d, hd, ?_⟩
  intro t ht v
  obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp (hS ht)
  obtain ⟨P, hPU, hP0, hP⟩ := hsol i t hti v
  let A : AdaptedIntervalSolution F T γ U t v := {
    domain := Set.Ioo (t - r i) (t + r i)
    open_domain := isOpen_Ioo
    preconnected_domain := isPreconnected_Ioo
    initial_mem := ⟨by linarith [hr i], by linarith [hr i]⟩
    domain_subset := hPU
    field := P
    adapted := hP
    initial_value := hP0
  }
  refine ⟨A, ?_⟩
  intro s hs
  change t - r i < s ∧ s < t + r i
  have hle := hdi i hi
  constructor <;> linarith [hs.1, hs.2]

theorem Icc_subset_of_uniform_open_intervals_at (D : Set ℝ) (hD : IsOpen D)
    (a c s0 : ℝ) (hs0 : s0 ∈ Set.Icc a c) (h0 : s0 ∈ D) (r : ℝ) (hr : 0 < r)
    (hstep : ∀ t ∈ Set.Icc a c, t ∈ D → Set.Ioo (t - r) (t + r) ⊆ D) :
    Set.Icc a c ⊆ D := by
  let E := Set.Icc a c
  letI : PreconnectedSpace E := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let A : Set E := {t | (t : ℝ) ∈ D}
  have hopen : IsOpen A := hD.preimage continuous_subtype_val
  have hcompl : IsOpen Aᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hN : Set.Ioo ((t : ℝ) - r) ((t : ℝ) + r) ∈ 𝓝 (t : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [continuousAt_subtype_val.preimage_mem_nhds hN] with z hz
    change (z : ℝ) ∉ D
    intro hzD
    apply ht
    exact hstep z z.property hzD ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hcompl, hopen⟩
    ⟨⟨s0, hs0⟩, h0⟩
  intro s hs
  have hm : (⟨s, hs⟩ : E) ∈ A := by rw [hAll]; trivial
  exact hm

theorem exists_adaptedFieldOn_Icc {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (a c s0 : ℝ) (hKU : Set.Icc a c ⊆ U) (hs0 : s0 ∈ Set.Icc a c)
    (v0 : TangentSpace (𝓡 n) (γ s0)) :
    ∃ (D : Set ℝ) (P : ∀ t, TangentSpace (𝓡 n) (γ t)),
      IsOpen D ∧ IsPreconnected D ∧ Set.Icc a c ⊆ D ∧ D ⊆ U ∧
        P s0 = v0 ∧ IsAdaptedFieldOn F T γ P D := by
  let A := maximalAdaptedSolution F T b hb hwindow γ U hU htime hγ s0 (hKU hs0) v0
  obtain ⟨d, hd, hrestart⟩ := exists_uniform_adaptedRestartRadius F T b hb hwindow
    γ U hU htime hγ (Set.Icc a c) isCompact_Icc hKU
  have hcover : Set.Icc a c ⊆ A.domain := by
    apply Icc_subset_of_uniform_open_intervals_at A.domain A.open_domain a c s0 hs0
      A.initial_mem d hd
    intro t ht htA
    obtain ⟨B, hB⟩ := hrestart t ht (A.field t)
    exact hB.trans (maximalAdaptedDomain_contains_restart F T b hb hwindow γ U hU
      htime hγ s0 (hKU hs0) v0 t htA B)
  exact ⟨A.domain, A.field, A.open_domain, A.preconnected_domain, hcover,
    A.domain_subset, A.initial_value, A.adapted⟩

end PoincareConjecture.Proofs.M09
