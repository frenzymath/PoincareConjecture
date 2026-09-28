import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Continuation.Local
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Continuation.Uniqueness










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

structure AdaptedIntervalSolution {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀)) where
  domain : Set ℝ
  open_domain : IsOpen domain
  preconnected_domain : IsPreconnected domain
  initial_mem : s₀ ∈ domain
  domain_subset : domain ⊆ U
  field : ∀ s, TangentSpace (𝓡 n) (γ s)
  adapted : IsAdaptedFieldOn F T γ field domain
  initial_value : field s₀ = v₀

theorem nonempty_adaptedIntervalSolution {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    Nonempty (AdaptedIntervalSolution F T γ U s₀ v₀) := by
  obtain ⟨W, d, _, hsW, _, hd, hsolve⟩ :=
    exists_uniform_local_isAdaptedFieldOn F T γ U hU htime hγ s₀ hs₀
  obtain ⟨P, hIU, hP₀, hP⟩ := hsolve s₀ hsW v₀
  exact ⟨{
    domain := Ioo (s₀ - d) (s₀ + d)
    open_domain := isOpen_Ioo
    preconnected_domain := isPreconnected_Ioo
    initial_mem := ⟨by linarith, by linarith⟩
    domain_subset := hIU
    field := P
    adapted := hP
    initial_value := hP₀ }⟩

theorem AdaptedIntervalSolution.eqOn {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {U : Set ℝ} {s₀ : ℝ} {v₀ : TangentSpace (𝓡 n) (γ s₀)}
    (A B : AdaptedIntervalSolution F T γ U s₀ v₀)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U) :
    ∀ s ∈ A.domain ∩ B.domain, A.field s = B.field s :=
  adaptedField_eqOn F T γ A.field B.field (A.domain ∩ B.domain)
    (A.open_domain.inter B.open_domain)
    (A.preconnected_domain.ordConnected.inter B.preconnected_domain.ordConnected).isPreconnected
    (fun s hs ↦ htime s (A.domain_subset hs.1))
    (hγ.mono (fun _ hs ↦ A.domain_subset hs.1))
    (A.adapted.mono inter_subset_left) (B.adapted.mono inter_subset_right)
    s₀ ⟨A.initial_mem, B.initial_mem⟩ (A.initial_value.trans B.initial_value.symm)

def maximalAdaptedDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀)) : Set ℝ :=
  ⋃ A : AdaptedIntervalSolution F T γ U s₀ v₀, A.domain

def maximalAdaptedField {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀))
    (s : ℝ) : TangentSpace (𝓡 n) (γ s) := by
  classical
  exact if hs : s ∈ maximalAdaptedDomain F T γ U s₀ v₀ then
    (Classical.choose (mem_iUnion.mp hs)).field s else 0

theorem isOpen_maximalAdaptedDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    IsOpen (maximalAdaptedDomain F T γ U s₀ v₀) := isOpen_iUnion fun A ↦ A.open_domain

theorem isPreconnected_maximalAdaptedDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    IsPreconnected (maximalAdaptedDomain F T γ U s₀ v₀) :=
  isPreconnected_iUnion ⟨s₀, mem_iInter.mpr (fun A ↦ A.initial_mem)⟩
    (fun A ↦ A.preconnected_domain)

theorem maximalAdaptedDomain_subset {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    maximalAdaptedDomain F T γ U s₀ v₀ ⊆ U := by
  intro s hs
  obtain ⟨A, hsA⟩ := mem_iUnion.mp hs
  exact A.domain_subset hsA

theorem AdaptedIntervalSolution.domain_subset_maximal {J : Set ℝ}
    {F : RicciFlow n M J} {T : ℝ} {γ : ℝ → M} {U : Set ℝ} {s₀ : ℝ}
    {v₀ : TangentSpace (𝓡 n) (γ s₀)} (A : AdaptedIntervalSolution F T γ U s₀ v₀) :
    A.domain ⊆ maximalAdaptedDomain F T γ U s₀ v₀ :=
  fun _ hs ↦ mem_iUnion.mpr ⟨A, hs⟩

theorem maximalAdaptedField_eqOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀))
    (A : AdaptedIntervalSolution F T γ U s₀ v₀) :
    ∀ s ∈ A.domain, maximalAdaptedField F T γ U s₀ v₀ s = A.field s := by
  intro s hs
  have hsD := A.domain_subset_maximal hs
  let B := Classical.choose (mem_iUnion.mp hsD)
  have hsB : s ∈ B.domain := Classical.choose_spec (mem_iUnion.mp hsD)
  unfold maximalAdaptedField
  rw [dif_pos hsD]
  exact B.eqOn A htime hγ s ⟨hsB, hs⟩

theorem maximalAdaptedField_adapted {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (s₀ : ℝ) (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    IsAdaptedFieldOn F T γ (maximalAdaptedField F T γ U s₀ v₀)
      (maximalAdaptedDomain F T γ U s₀ v₀) := by
  apply IsAdaptedFieldOn.of_locally
  intro s hs
  obtain ⟨A, hsA⟩ := mem_iUnion.mp hs
  refine ⟨A.field, A.domain, A.open_domain, hsA, A.adapted, ?_⟩
  filter_upwards [A.open_domain.mem_nhds hsA] with t ht
  exact maximalAdaptedField_eqOn F T γ U htime hγ s₀ v₀ A t ht

def maximalAdaptedSolution {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    AdaptedIntervalSolution F T γ U s₀ v₀ where
  domain := maximalAdaptedDomain F T γ U s₀ v₀
  open_domain := isOpen_maximalAdaptedDomain F T γ U s₀ v₀
  preconnected_domain := isPreconnected_maximalAdaptedDomain F T γ U s₀ v₀
  initial_mem := by
    obtain ⟨A⟩ := nonempty_adaptedIntervalSolution F T γ U hU htime hγ s₀ hs₀ v₀
    exact A.domain_subset_maximal A.initial_mem
  domain_subset := maximalAdaptedDomain_subset F T γ U s₀ v₀
  field := maximalAdaptedField F T γ U s₀ v₀
  adapted := maximalAdaptedField_adapted F T γ U htime hγ s₀ v₀
  initial_value := by
    obtain ⟨A⟩ := nonempty_adaptedIntervalSolution F T γ U hU htime hγ s₀ hs₀ v₀
    exact (maximalAdaptedField_eqOn F T γ U htime hγ s₀ v₀ A s₀
      A.initial_mem).trans A.initial_value

theorem exists_adaptedIntervalSolution_union {J : Set ℝ} {F : RicciFlow n M J}
    {T : ℝ} {γ : ℝ → M} {U : Set ℝ} {s₀ : ℝ} {v₀ : TangentSpace (𝓡 n) (γ s₀)}
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (A : AdaptedIntervalSolution F T γ U s₀ v₀) (s : ℝ) (hs : s ∈ A.domain)
    (B : AdaptedIntervalSolution F T γ U s (A.field s)) :
    ∃ C : AdaptedIntervalSolution F T γ U s₀ v₀,
      C.domain = A.domain ∪ B.domain := by
  classical
  have hp := adaptedField_eqOn F T γ A.field B.field
    (A.domain ∩ B.domain) (A.open_domain.inter B.open_domain)
    (A.preconnected_domain.ordConnected.inter B.preconnected_domain.ordConnected).isPreconnected
    (fun r hr ↦ htime r (A.domain_subset hr.1))
    (hγ.mono (fun _ hr ↦ A.domain_subset hr.1))
    (A.adapted.mono inter_subset_left) (B.adapted.mono inter_subset_right)
    s ⟨hs, B.initial_mem⟩ B.initial_value.symm
  let P : ∀ t, TangentSpace (𝓡 n) (γ t) :=
    fun t ↦ if t ∈ A.domain then A.field t else B.field t
  have heA : ∀ t ∈ A.domain, P t = A.field t := fun _ ht ↦ if_pos ht
  have heB : ∀ t ∈ B.domain, P t = B.field t := by
    intro t ht
    by_cases htA : t ∈ A.domain
    · exact (heA t htA).trans (hp t ⟨htA, ht⟩)
    · exact if_neg htA
  have hP : IsAdaptedFieldOn F T γ P (A.domain ∪ B.domain) := by
    apply IsAdaptedFieldOn.of_locally
    intro t ht
    rcases ht with ht | ht
    · refine ⟨A.field, A.domain, A.open_domain, ht, A.adapted, ?_⟩
      filter_upwards [A.open_domain.mem_nhds ht] with r hr using heA r hr
    · refine ⟨B.field, B.domain, B.open_domain, ht, B.adapted, ?_⟩
      filter_upwards [B.open_domain.mem_nhds ht] with r hr using heB r hr
  exact ⟨{
    domain := A.domain ∪ B.domain
    open_domain := A.open_domain.union B.open_domain
    preconnected_domain := A.preconnected_domain.union s hs B.initial_mem B.preconnected_domain
    initial_mem := Or.inl A.initial_mem
    domain_subset := fun _ ht ↦ ht.elim (fun h ↦ A.domain_subset h)
      (fun h ↦ B.domain_subset h)
    field := P
    adapted := hP
    initial_value := (heA s₀ A.initial_mem).trans A.initial_value }, rfl⟩

theorem maximalAdaptedDomain_contains_restart {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (v₀ : TangentSpace (𝓡 n) (γ s₀))
    (s : ℝ) (hs : s ∈ maximalAdaptedDomain F T γ U s₀ v₀)
    (B : AdaptedIntervalSolution F T γ U s (maximalAdaptedField F T γ U s₀ v₀ s)) :
    B.domain ⊆ maximalAdaptedDomain F T γ U s₀ v₀ := by
  let A := maximalAdaptedSolution F T γ U hU htime hγ s₀ hs₀ v₀
  obtain ⟨C, hC⟩ := exists_adaptedIntervalSolution_union htime hγ A s hs B
  intro t ht
  exact C.domain_subset_maximal (hC.symm ▸ Or.inr ht)

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
