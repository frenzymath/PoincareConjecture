import PoincareConjecture.Proofs.M09.PullbackCoordinate
import PoincareConjecture.Proofs.M09.CompactFieldExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "P" => ModelWithCorners.prod (𝓘(ℝ, ℝ)) (𝓡 n)

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_pullbackDerivativeExtensionOn_compact {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (γ s))
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) (htime : K ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (E : ParametricAlongCurveExtensionOn K γ Y) :
    Nonempty (ParametricAlongCurveExtensionOn K γ
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E)) := by
  classical
  let U0 := (U ∩ (fun s ↦ (s, γ s)) ⁻¹' E.domain) ∩
    Set.Ioo (-Real.sqrt b) (Real.sqrt b)
  have hg : ContMDiffOn (𝓘(ℝ, ℝ)) P ∞ (fun s ↦ (s, γ s)) U :=
    contMDiffOn_id.prodMk hγ
  have hU0 : IsOpen U0 :=
    (hg.continuousOn.isOpen_inter_preimage hU E.open_domain).inter isOpen_Ioo
  have hKU0 : K ⊆ U0 := fun s hs ↦ ⟨⟨hKU hs, E.graph_mem s hs⟩, htime hs⟩
  have hγ0 : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U0 := hγ.mono (fun _ h ↦ h.1.1)
  have hY0 : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨γ s, E.extension s (γ s)⟩ : TangentBundle (𝓡 n) M)) U0 :=
    E.smooth.comp (hg.mono (fun _ h ↦ h.1.1)) (fun _ h ↦ h.1.2)
  let W : ℝ → Set ℝ := fun t ↦ U0 ∩ γ ⁻¹' (chartAt V (γ t)).source
  have hW (t : ℝ) : IsOpen (W t) :=
    hγ0.continuousOn.isOpen_inter_preimage hU0 (chartAt V (γ t)).open_source
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover W (fun t ht ↦
    (hW t).mem_nhds ⟨hKU0 ht, mem_chart_source V (γ t)⟩)
  have hcover' : K ⊆ ⋃ i : S, W i := by
    intro s hs
    obtain ⟨t, htS, ht⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact Set.mem_iUnion.mpr ⟨⟨t, htS⟩, ht⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ))
    hK.isClosed (fun i : S ↦ W i) (fun i ↦ hW i) hcover'
  let a : S → ℝ → V := fun i s ↦ (chartAt V (γ i)) (γ s)
  let v : S → ℝ → V := fun i s ↦
    (tangentChartPhase (γ i) (⟨γ s, E.extension s (γ s)⟩ : TangentBundle (𝓡 n) M)).2
  have ha (i : S) : ContDiffOn ℝ ∞ (a i) (W i) :=
    (contMDiffOn_chart.comp (hγ0.mono Set.inter_subset_left) (fun _ h ↦ h.2)).contDiffOn
  have hv (i : S) : ContDiffOn ℝ ∞ (v i) (W i) :=
    ((tangentChartPhase_contMDiffOn (γ i)).comp (hY0.mono Set.inter_subset_left)
      (fun _ h ↦ h.2)).contDiffOn.snd
  let d : S → ℝ → V := fun i s ↦ deriv (v i) s +
    coordinateConnection (squareChartMetric F T (γ i)) (s, a i s) (deriv (a i) s) (v i s)
  have hd (i : S) : ContDiffOn ℝ ∞ (d i) (W i) := by
    have hC := coordinateConnection_smooth (squareChartMetric F T (γ i))
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt V (γ i)).target)
      (isOpen_Ioo.prod (chartAt V (γ i)).open_target)
      (squareChartMetric_smooth F T b hb hwindow (γ i))
      (fun z hz w hw ↦ squareChartMetric_pos F T (γ i) z hz.2 w hw)
    have hmap : ContDiffOn ℝ ∞
        (fun s ↦ ((s, a i s), (deriv (a i) s, v i s))) (W i) :=
      (contDiffOn_id.prodMk (ha i)).prodMk
        (((ha i).deriv_of_isOpen (hW i) (by simp)).prodMk (hv i))
    have hmaps : Set.MapsTo (fun s ↦ ((s, a i s), (deriv (a i) s, v i s))) (W i)
        {q : (ℝ × V) × (V × V) |
          q.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt V (γ i)).target} :=
      fun s hs ↦ ⟨hs.1.2, (chartAt V (γ i)).map_source hs.2⟩
    have hc := hC.comp hmap hmaps
    exact ((hv i).deriv_of_isOpen (hW i) (by simp)).add hc
  have hdvalue (i : S) (s : ℝ) (hs : s ∈ K ∩ W i) :
      chartVectorField (γ i) (d i s) (γ s) =
        pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E s := by
    symm
    apply pullbackCovariantDerivative_eq_chart F T b hb hwindow (γ i) γ Y K (W i) E
      (hW i) (hγ0.mono Set.inter_subset_left) (fun r hr ↦ hr.2) (v i) (hv i)
      ?_ s hs.1 hs.2 (hKd s hs.1) (htime hs.1)
    intro r hr
    exact (chartVectorField_differential (γ i) (γ r) (E.extension r (γ r)) hr.2.2).trans
      (E.agrees r hr.1)
  let X : S → ℝ → (x : M) → TangentSpace (𝓡 n) x :=
    fun i s ↦ chartVectorField (γ i) (d i s)
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
  let H : ℝ → (x : M) → TangentSpace (𝓡 n) x := fun s x ↦ ∑ i : S, ρ i s • X i s x
  have hH : ContMDiffOn P ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (⟨z.2, H z.1 z.2⟩ : TangentBundle (𝓡 n) M)) D :=
    weightedParametricField_smooth (fun i s ↦ ρ i s)
      (fun i ↦ (ρ i).contMDiff.contDiff) (fun i ↦ W i)
      (fun i ↦ (chartAt V (γ i)).source) (fun i ↦ hW i)
      (fun i ↦ (chartAt V (γ i)).open_source) X
      (fun i ↦ chartVectorField_param_smooth (γ i) (d i) (W i) (hd i))
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
    H s (γ s) = ∑ i : S, ρ i s •
        pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E s := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ρ i s = 0
      · simp [hi]
      · rw [show X i s (γ s) = _ from hdvalue i s
          ⟨hs, hρ i (subset_tsupport (ρ i) (Function.mem_support.mpr hi))⟩]
    _ = (∑ i : S, ρ i s) •
        pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E s := (Finset.sum_smul ..).symm
    _ = _ := by rw [hsum, one_smul]

end PoincareConjecture.Proofs.M09
