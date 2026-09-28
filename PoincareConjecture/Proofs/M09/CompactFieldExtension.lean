import PoincareConjecture.Proofs.M09.ParametricFieldSum
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.SmoothTangentChartPhase
import Mathlib.Geometry.Manifold.PartitionOfUnity








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "P" => ModelWithCorners.prod (𝓘(ℝ, ℝ)) (𝓡 n)

set_option backward.isDefEq.respectTransparency false in
theorem chartVectorField_differential (p x : M) (v : TangentSpace (𝓡 n) x)
    (hx : x ∈ (chartAt V p).source) :
    chartVectorField p (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) x v) x = v := by
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) x).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hx, rfl⟩
  exact hi.inverse_apply_self v

theorem nonempty_parametricFieldExtensionOn_compact (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) (U K : Set ℝ)
    (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨γ s, Y s⟩ : TangentBundle (𝓡 n) M)) U) :
    Nonempty (ParametricAlongCurveExtensionOn (n := n) K γ Y) := by
  classical
  let W : ℝ → Set ℝ := fun t ↦ U ∩ γ ⁻¹' (chartAt V (γ t)).source
  have hW (t : ℝ) : IsOpen (W t) :=
    hγ.continuousOn.isOpen_inter_preimage hU (chartAt V (γ t)).open_source
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover W (fun t ht ↦
    (hW t).mem_nhds ⟨hKU ht, mem_chart_source V (γ t)⟩)
  have hcover' : K ⊆ ⋃ i : S, W i := by
    intro s hs
    obtain ⟨t, htS, ht⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact Set.mem_iUnion.mpr ⟨⟨t, htS⟩, ht⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ))
    hK.isClosed (fun i : S ↦ W i) (fun i ↦ hW i) hcover'
  let v : S → ℝ → V := fun i s ↦
    (tangentChartPhase (γ i) (⟨γ s, Y s⟩ : TangentBundle (𝓡 n) M)).2
  have hv (i : S) : ContDiffOn ℝ ∞ (v i) (W i) := by
    have hc := (tangentChartPhase_contMDiffOn (γ i)).comp
      (hY.mono (show W i ⊆ U from Set.inter_subset_left)) (fun s hs ↦ hs.2)
    exact hc.contDiffOn.snd
  let X : S → ℝ → (x : M) → TangentSpace (𝓡 n) x :=
    fun i s ↦ chartVectorField (γ i) (v i s)
  let D : Set (ℝ × M) := ⋂ i : S,
    ((tsupport (ρ i))ᶜ ×ˢ Set.univ) ∪ (W i ×ˢ (chartAt V (γ i)).source)
  have hD : IsOpen D := isOpen_iInter_of_finite fun i ↦
    ((isClosed_tsupport (ρ i)).isOpen_compl.prod isOpen_univ).union
      ((hW i).prod (chartAt V (γ i)).open_source)
  have hgraph : ∀ s ∈ K, (s, γ s) ∈ D := by
    intro s hs
    apply Set.mem_iInter.mpr
    intro i
    by_cases hi : s ∈ tsupport (ρ i)
    · exact Or.inr ⟨hρ i hi, (hρ i hi).2⟩
    · exact Or.inl ⟨hi, Set.mem_univ _⟩
  let H : ℝ → (x : M) → TangentSpace (𝓡 n) x :=
    fun s x ↦ ∑ i : S, ρ i s • X i s x
  have hH : ContMDiffOn P ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (⟨z.2, H z.1 z.2⟩ : TangentBundle (𝓡 n) M)) D :=
    weightedParametricField_smooth (fun i s ↦ ρ i s)
      (fun i ↦ (ρ i).contMDiff.contDiff) (fun i ↦ W i)
      (fun i ↦ (chartAt V (γ i)).source) (fun i ↦ hW i)
      (fun i ↦ (chartAt V (γ i)).open_source) X
      (fun i ↦ chartVectorField_param_smooth (γ i) (v i) (W i) (hv i))
  refine ⟨{
    extension := H
    domain := D
    open_domain := hD
    graph_mem := hgraph
    smooth := hH
    agrees := ?_
  }⟩
  intro s hs
  have hsum : ∑ i : S, ρ i s = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hs
  calc
    H s (γ s) = ∑ i : S, ρ i s • Y s := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ρ i s = 0
      · simp [hi]
      · have hsi : s ∈ W i := hρ i (subset_tsupport (ρ i) (Function.mem_support.mpr hi))
        have hvalue : X i s (γ s) = Y s :=
          chartVectorField_differential (γ i) (γ s) (Y s) hsi.2
        rw [hvalue]
    _ = (∑ i : S, ρ i s) • Y s := (Finset.sum_smul ..).symm
    _ = Y s := by rw [hsum, one_smul]

end PoincareConjecture.Proofs.M09
