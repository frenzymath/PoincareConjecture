import PoincareConjecture.Proofs.M09.MaximalAdaptedField
import Mathlib.Data.Set.Piecewise

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem exists_adaptedIntervalSolution_union {J : Set ℝ} {F : RicciFlow n M J}
    {T : ℝ} {γ : ℝ → M} {U : Set ℝ} {s0 : ℝ} {v0 : TangentSpace (𝓡 n) (γ s0)}
    (b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (A : AdaptedIntervalSolution F T γ U s0 v0) (s : ℝ) (hs : s ∈ A.domain)
    (B : AdaptedIntervalSolution F T γ U s (A.field s)) :
    ∃ C : AdaptedIntervalSolution F T γ U s0 v0,
      C.domain = A.domain ∪ B.domain ∧
        (∀ t ∈ A.domain, C.field t = A.field t) ∧
        (∀ t ∈ B.domain, C.field t = B.field t) := by
  classical
  have hp := adaptedField_eqOn F T b hb hwindow γ A.field B.field
    (A.domain ∩ B.domain) (A.open_domain.inter B.open_domain)
    (A.preconnected_domain.ordConnected.inter B.preconnected_domain.ordConnected).isPreconnected
    (fun _ ht ↦ htime (A.domain_subset ht.1))
    (hγ.mono (fun _ ht ↦ A.domain_subset ht.1))
    (A.adapted.mono Set.inter_subset_left) (B.adapted.mono Set.inter_subset_right)
    s ⟨hs, B.initial_mem⟩ B.initial_value.symm
  let P : ∀ t, TangentSpace (𝓡 n) (γ t) :=
    fun t ↦ if t ∈ A.domain then A.field t else B.field t
  have heA : ∀ t ∈ A.domain, P t = A.field t := fun t ht ↦ if_pos ht
  have heB : ∀ t ∈ B.domain, P t = B.field t := by
    intro t ht
    by_cases htA : t ∈ A.domain
    · exact (heA t htA).trans (hp t ⟨htA, ht⟩)
    · exact if_neg htA
  have hgA : ∀ t ∈ A.domain, ∀ᶠ r in 𝓝 t, P r = A.field r := by
    intro t ht
    filter_upwards [A.open_domain.mem_nhds ht] with r hr using heA r hr
  have hgB : ∀ t ∈ B.domain, ∀ᶠ r in 𝓝 t, P r = B.field r := by
    intro t ht
    filter_upwards [B.open_domain.mem_nhds ht] with r hr using heB r hr
  have hP : IsAdaptedFieldOn F T γ P (A.domain ∪ B.domain) := by
    apply IsAdaptedFieldOn.of_locally
    intro t ht
    rcases ht with ht | ht
    · exact ⟨A.field, A.domain, A.open_domain, ht, A.adapted, hgA t ht⟩
    · exact ⟨B.field, B.domain, B.open_domain, ht, B.adapted, hgB t ht⟩
  let C : AdaptedIntervalSolution F T γ U s0 v0 := {
    domain := A.domain ∪ B.domain
    open_domain := A.open_domain.union B.open_domain
    preconnected_domain := A.preconnected_domain.union s hs B.initial_mem B.preconnected_domain
    initial_mem := Or.inl A.initial_mem
    domain_subset := fun _ ht ↦ ht.elim (fun h ↦ A.domain_subset h) (fun h ↦ B.domain_subset h)
    field := P
    adapted := hP
    initial_value := (heA s0 A.initial_mem).trans A.initial_value
  }
  exact ⟨C, rfl, heA, heB⟩

theorem maximalAdaptedDomain_contains_restart {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (s0 : ℝ) (hs0 : s0 ∈ U) (v0 : TangentSpace (𝓡 n) (γ s0))
    (s : ℝ) (hs : s ∈ maximalAdaptedDomain F T γ U s0 v0)
    (B : AdaptedIntervalSolution F T γ U s (maximalAdaptedField F T γ U s0 v0 s)) :
    B.domain ⊆ maximalAdaptedDomain F T γ U s0 v0 := by
  let A := maximalAdaptedSolution F T b hb hwindow γ U hU htime hγ s0 hs0 v0
  obtain ⟨C, hC, _, _⟩ := exists_adaptedIntervalSolution_union b hb hwindow htime hγ A s hs B
  intro t ht
  exact C.domain_subset_maximal (hC.symm ▸ Or.inr ht)

end PoincareConjecture.Proofs.M09
