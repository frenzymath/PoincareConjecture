import PoincareConjecture.Proofs.M09.AdaptedFieldUniqueness
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

structure AdaptedIntervalSolution {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (U : Set ℝ) (s0 : ℝ) (v0 : TangentSpace (𝓡 n) (γ s0)) where
  domain : Set ℝ
  open_domain : IsOpen domain
  preconnected_domain : IsPreconnected domain
  initial_mem : s0 ∈ domain
  domain_subset : domain ⊆ U
  field : ∀ t, TangentSpace (𝓡 n) (γ t)
  adapted : IsAdaptedFieldOn F T γ field domain
  initial_value : field s0 = v0

theorem nonempty_adaptedIntervalSolution {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (s0 : ℝ) (hs0 : s0 ∈ U) (v0 : TangentSpace (𝓡 n) (γ s0)) :
    Nonempty (AdaptedIntervalSolution F T γ U s0 v0) := by
  obtain ⟨W, d, _, hsW, _, hd, hsolve⟩ :=
    exists_uniform_local_isAdaptedFieldOn F T b hb hwindow γ U hU htime hγ s0 hs0
  obtain ⟨P, hPU, hP0, hP⟩ := hsolve s0 hsW v0
  exact ⟨{
    domain := Set.Ioo (s0 - d) (s0 + d)
    open_domain := isOpen_Ioo
    preconnected_domain := isPreconnected_Ioo
    initial_mem := ⟨by linarith, by linarith⟩
    domain_subset := hPU
    field := P
    adapted := hP
    initial_value := hP0
  }⟩

theorem AdaptedIntervalSolution.eqOn {J : Set ℝ} [T2Space M] {F : RicciFlow n M J}
    {T : ℝ} {γ : ℝ → M} {U : Set ℝ} {s0 : ℝ} {v0 : TangentSpace (𝓡 n) (γ s0)}
    (A B : AdaptedIntervalSolution F T γ U s0 v0)
    (b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) :
    ∀ t ∈ A.domain ∩ B.domain, A.field t = B.field t := by
  exact adaptedField_eqOn F T b hb hwindow γ A.field B.field (A.domain ∩ B.domain)
    (A.open_domain.inter B.open_domain)
    (A.preconnected_domain.ordConnected.inter B.preconnected_domain.ordConnected).isPreconnected
    (fun _ ht ↦ htime (A.domain_subset ht.1))
    (hγ.mono (fun _ ht ↦ A.domain_subset ht.1))
    (A.adapted.mono Set.inter_subset_left) (B.adapted.mono Set.inter_subset_right)
    s0 ⟨A.initial_mem, B.initial_mem⟩ (A.initial_value.trans B.initial_value.symm)

end PoincareConjecture.Proofs.M09
