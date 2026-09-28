import PoincareConjecture.Proofs.M09.LocalAdaptedEquation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

structure IsAdaptedFieldOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t)) (U : Set ℝ) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
    (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U
  equation : ∀ s ∈ U, LocalAdaptedEquation F T γ P s

theorem IsAdaptedFieldOn.mono {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {P : ∀ t, TangentSpace (𝓡 n) (γ t)} {U V : Set ℝ}
    (h : IsAdaptedFieldOn F T γ P U) (hVU : V ⊆ U) : IsAdaptedFieldOn F T γ P V :=
  ⟨h.smooth.mono hVU, fun s hs ↦ h.equation s (hVU hs)⟩

theorem IsAdaptedFieldOn.congr {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {P Q : ∀ t, TangentSpace (𝓡 n) (γ t)} {U : Set ℝ}
    (h : IsAdaptedFieldOn F T γ P U) (hU : IsOpen U)
    (heq : ∀ t ∈ U, P t = Q t) : IsAdaptedFieldOn F T γ Q U := by
  refine ⟨h.smooth.congr (fun t ht ↦ ?_), ?_⟩
  · rw [heq t ht]
  · intro s hs
    apply (h.equation s hs).congr
    filter_upwards [hU.mem_nhds hs] with t ht using heq t ht

theorem IsAdaptedFieldOn.of_locally {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {P : ∀ t, TangentSpace (𝓡 n) (γ t)} {U : Set ℝ}
    (h : ∀ s ∈ U, ∃ (Q : ∀ t, TangentSpace (𝓡 n) (γ t)) (V : Set ℝ),
      IsOpen V ∧ s ∈ V ∧ IsAdaptedFieldOn F T γ Q V ∧
        ∀ᶠ t in 𝓝 s, P t = Q t) : IsAdaptedFieldOn F T γ P U := by
  have hp : ∀ s ∈ U,
      ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) s ∧
      LocalAdaptedEquation F T γ P s := by
    intro s hs
    obtain ⟨Q, V, hV, hsV, hQ, heq⟩ := h s hs
    have he : (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) =ᶠ[𝓝 s]
        (fun t ↦ (⟨γ t, Q t⟩ : TangentBundle (𝓡 n) M)) := by
      filter_upwards [heq] with t ht
      rw [ht]
    exact ⟨(hQ.smooth.contMDiffAt (hV.mem_nhds hsV)).congr_of_eventuallyEq he,
      (hQ.equation s hsV).congr (heq.mono (fun _ ht ↦ ht.symm))⟩
  exact ⟨fun s hs ↦ (hp s hs).1.contMDiffWithinAt, fun s hs ↦ (hp s hs).2⟩

theorem exists_uniform_local_isAdaptedFieldOn {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) (s0 : ℝ) (hs0 : s0 ∈ U) :
    ∃ (W : Set ℝ) (d : ℝ), IsOpen W ∧ s0 ∈ W ∧ W ⊆ U ∧ 0 < d ∧
      ∀ t0 ∈ W, ∀ v0 : TangentSpace (𝓡 n) (γ t0),
        ∃ P : ∀ t, TangentSpace (𝓡 n) (γ t),
          Set.Ioo (t0 - d) (t0 + d) ⊆ U ∧ P t0 = v0 ∧
            IsAdaptedFieldOn F T γ P (Set.Ioo (t0 - d) (t0 + d)) := by
  obtain ⟨W, d, hW, hsW, hWU, hd, hsolve⟩ :=
    exists_uniform_local_adapted_field F T b hb hwindow γ U hU htime hγ s0 hs0
  refine ⟨W, d, hW, hsW, hWU, hd, ?_⟩
  intro t0 ht0 v0
  obtain ⟨P, hIU, hP0, hP, H, heq⟩ := hsolve t0 ht0 v0
  refine ⟨P, hIU, hP0, hP, ?_⟩
  intro s hs
  exact localAdaptedEquation_of_pullback F T b hb hwindow γ P _ _ H
    isOpen_Ioo (hγ.mono hIU) hP s hs hs (isOpen_Ioo.uniqueDiffOn s hs)
    (htime (hIU hs)) (heq s hs)

theorem IsAdaptedFieldOn.exists_extension_compact {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) (htime : K ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) (hP : IsAdaptedFieldOn F T γ P U) :
    ∃ H : ParametricAlongCurveExtensionOn (n := n) K γ P,
      ∀ s ∈ K, ∀ w : TangentSpace (𝓡 n) (γ s),
        (F.metric (T - s ^ 2)).inner (γ s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s) w =
          -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) w := by
  obtain ⟨H⟩ := nonempty_parametricFieldExtensionOn_compact γ P U K hU hKU hK hγ hP.smooth
  refine ⟨H, ?_⟩
  intro s hs w
  exact pullback_adapted_of_localAdaptedEquation F T b hb hwindow γ P K U H
    hU hγ hP.smooth s hs (hKU hs) (hKd s hs) (htime hs) (hP.equation s (hKU hs)) w

end PoincareConjecture.Proofs.M09
