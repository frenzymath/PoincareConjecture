import PoincareConjecture.Proofs.M09.AdaptedIntervalSolution

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def maximalAdaptedDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0)) : Set ℝ :=
  ⋃ A : AdaptedIntervalSolution F T γ U s0 v0, A.domain

noncomputable def maximalAdaptedField {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0))
    (s : ℝ) : TangentSpace (𝓡 n) (γ s) := by
  classical
  exact if hs : s ∈ maximalAdaptedDomain F T γ U s0 v0 then
    (Classical.choose (Set.mem_iUnion.mp hs)).field s else 0

theorem isOpen_maximalAdaptedDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0)) :
    IsOpen (maximalAdaptedDomain F T γ U s0 v0) := isOpen_iUnion fun A ↦ A.open_domain

theorem isPreconnected_maximalAdaptedDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0)) :
    IsPreconnected (maximalAdaptedDomain F T γ U s0 v0) :=
  isPreconnected_iUnion ⟨s0, Set.mem_iInter.mpr (fun A ↦ A.initial_mem)⟩
    (fun A ↦ A.preconnected_domain)

theorem maximalAdaptedDomain_subset {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0)) :
    maximalAdaptedDomain F T γ U s0 v0 ⊆ U := by
  intro s hs
  obtain ⟨A, hsA⟩ := Set.mem_iUnion.mp hs
  exact A.domain_subset hsA

theorem AdaptedIntervalSolution.domain_subset_maximal {J : Set ℝ}
    {F : RicciFlow n M J} {T : ℝ} {γ : ℝ → M} {U : Set ℝ} {s0 : ℝ}
    {v0 : TangentSpace (𝓡 n) (γ s0)} (A : AdaptedIntervalSolution F T γ U s0 v0) :
    A.domain ⊆ maximalAdaptedDomain F T γ U s0 v0 :=
  fun _ hs ↦ Set.mem_iUnion.mpr ⟨A, hs⟩

theorem maximalAdaptedField_eqOn {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0))
    (A : AdaptedIntervalSolution F T γ U s0 v0) :
    ∀ s ∈ A.domain, maximalAdaptedField F T γ U s0 v0 s = A.field s := by
  intro s hs
  have hsD := A.domain_subset_maximal hs
  let B := Classical.choose (Set.mem_iUnion.mp hsD)
  have hsB : s ∈ B.domain := Classical.choose_spec (Set.mem_iUnion.mp hsD)
  unfold maximalAdaptedField
  rw [dif_pos hsD]
  exact B.eqOn A b hb hwindow htime hγ s ⟨hsB, hs⟩

theorem maximalAdaptedField_eventuallyEq {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0))
    (A : AdaptedIntervalSolution F T γ U s0 v0) (s : ℝ) (hs : s ∈ A.domain) :
    ∀ᶠ t in 𝓝 s, maximalAdaptedField F T γ U s0 v0 t = A.field t := by
  filter_upwards [A.open_domain.mem_nhds hs] with t ht
  exact maximalAdaptedField_eqOn F T b hb hwindow γ U htime hγ s0 v0 A t ht

theorem maximalAdaptedField_adapted {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0)) :
    IsAdaptedFieldOn F T γ (maximalAdaptedField F T γ U s0 v0)
      (maximalAdaptedDomain F T γ U s0 v0) := by
  apply IsAdaptedFieldOn.of_locally
  intro s hs
  obtain ⟨A, hsA⟩ := Set.mem_iUnion.mp hs
  exact ⟨A.field, A.domain, A.open_domain, hsA, A.adapted,
    maximalAdaptedField_eventuallyEq F T b hb hwindow γ U htime hγ s0 v0 A s hsA⟩

noncomputable def maximalAdaptedSolution {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (s0 : ℝ) (hs0 : s0 ∈ U) (v0 : TangentSpace (𝓡 n) (γ s0)) :
    AdaptedIntervalSolution F T γ U s0 v0 where
  domain := maximalAdaptedDomain F T γ U s0 v0
  open_domain := isOpen_maximalAdaptedDomain F T γ U s0 v0
  preconnected_domain := isPreconnected_maximalAdaptedDomain F T γ U s0 v0
  initial_mem := by
    obtain ⟨A⟩ := nonempty_adaptedIntervalSolution F T b hb hwindow γ U hU htime hγ s0 hs0 v0
    exact A.domain_subset_maximal A.initial_mem
  domain_subset := maximalAdaptedDomain_subset F T γ U s0 v0
  field := maximalAdaptedField F T γ U s0 v0
  adapted := maximalAdaptedField_adapted F T b hb hwindow γ U htime hγ s0 v0
  initial_value := by
    obtain ⟨A⟩ := nonempty_adaptedIntervalSolution F T b hb hwindow γ U hU htime hγ s0 hs0 v0
    exact (maximalAdaptedField_eqOn F T b hb hwindow γ U htime hγ s0 v0 A s0
      A.initial_mem).trans A.initial_value

end PoincareConjecture.Proofs.M09
