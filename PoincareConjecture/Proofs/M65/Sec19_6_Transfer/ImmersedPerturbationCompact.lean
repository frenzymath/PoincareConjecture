import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationSeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))

private theorem angular_open_quotient : IsOpenQuotientMap ang := by
  refine ⟨m65AngularCircle_surjective,
    Proofs.M58.contDiff_angularPoint.continuous.subtype_mk _, ?_⟩
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← m65AngularCircle_map_nhds x]
  exact image_mem_map (hU.mem_nhds hx)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

theorem continuousOn_circle_family
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (V : Set P) (J : Set ℝ)
    (hV : IsOpen V) (hJ : IsOpen J)
    (hGamma : ContMDiffOn 𝓘(ℝ, (ℝ × P) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1) ((univ ×ˢ V) ×ˢ J)) :
    ContinuousOn (fun z : (LoopCircle × P) × ℝ => Gamma z.1.2 z.2 z.1.1)
      ((univ ×ˢ V) ×ˢ J) := by
  intro z hz
  obtain ⟨x, hx⟩ := m65AngularCircle_surjective z.1.1
  let Q := Prod.map (Prod.map ang (id : P → P)) (id : ℝ → ℝ)
  have hQ : IsOpenQuotientMap Q :=
    (angular_open_quotient.prodMap IsOpenQuotientMap.id).prodMap IsOpenQuotientMap.id
  have hraw := (hGamma.contMDiffAt
    (((isOpen_univ.prod hV).prod hJ).mem_nhds
      (show ((x, z.1.2), z.2) ∈ (univ ×ˢ V) ×ˢ J from
        ⟨⟨mem_univ _, hz.1.2⟩, hz.2⟩))).continuousAt
  have hcomp : ContinuousAt ((fun z : (LoopCircle × P) × ℝ =>
      Gamma z.1.2 z.2 z.1.1) ∘ Q) ((x, z.1.2), z.2) := by
    apply hraw.congr
    exact Filter.Eventually.of_forall (fun w => (Gamma w.1.2 w.2).boundary (ang w.1.1))
  have hresult := hQ.continuousAt_comp_iff.mp hcomp
  have hpoint : Q ((x, z.1.2), z.2) = z := by
    change ((ang x, z.1.2), z.2) = z
    rw [hx]
  rw [hpoint] at hresult
  exact hresult.continuousWithinAt

variable [T2Space M]

omit [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] in

theorem compact_separated_double_points
    (c : ℝ → LoopCircle → M) (K : Set ℝ) (hK : IsCompact K)
    (hc : ContinuousOn (fun z : LoopCircle × ℝ => c z.2 z.1) (univ ×ˢ K))
    (rho : ℝ) :
    IsCompact {z : (LoopCircle × LoopCircle) × ℝ |
      z.2 ∈ K ∧ rho ≤ dist z.1.1 z.1.2 ∧ c z.2 z.1.1 = c z.2 z.1.2} := by
  have hbase : IsCompact ((univ : Set (LoopCircle × LoopCircle)) ×ˢ K) :=
    isCompact_univ.prod hK
  have hleft : ContinuousOn (fun z : (LoopCircle × LoopCircle) × ℝ => c z.2 z.1.1)
      (univ ×ˢ K) := hc.comp (continuous_fst.fst.prodMk continuous_snd).continuousOn
        (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hright : ContinuousOn (fun z : (LoopCircle × LoopCircle) × ℝ => c z.2 z.1.2)
      (univ ×ˢ K) := hc.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn
        (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hdist : IsClosed {z : (LoopCircle × LoopCircle) × ℝ | rho ≤ dist z.1.1 z.1.2} :=
    isClosed_le continuous_const (continuous_fst.fst.dist continuous_fst.snd)
  have heq := hbase.isClosed.isClosed_eq hleft hright
  have hcompact := (hbase.of_isClosed_subset heq (fun _ hz => hz.1)).inter_right hdist
  convert hcompact using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, true_and]
  tauto

set_option maxHeartbeats 600000 in

theorem exists_double_point_capture
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (V : Set P) (J K : Set ℝ)
    (hV : IsOpen V) (hzero : (0 : P) ∈ V) (hJ : IsOpen J)
    (hK : IsCompact K) (hKJ : K ⊆ J)
    (hGamma : ContMDiffOn 𝓘(ℝ, (ℝ × P) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1) ((univ ×ˢ V) ×ˢ J))
    (rho : ℝ) (O : Set ((LoopCircle × LoopCircle) × ℝ)) (hO : IsOpen O)
    (hcover : ∀ z : (LoopCircle × LoopCircle) × ℝ, z.2 ∈ K →
      rho ≤ dist z.1.1 z.1.2 → Gamma 0 z.2 z.1.1 = Gamma 0 z.2 z.1.2 → z ∈ O) :
    ∃ delta : ℝ, 0 < delta ∧ ball (0 : P) delta ⊆ V ∧
      ∀ p ∈ ball (0 : P) delta, ∀ z : (LoopCircle × LoopCircle) × ℝ,
        z.2 ∈ K → rho ≤ dist z.1.1 z.1.2 →
          Gamma p z.2 z.1.1 = Gamma p z.2 z.1.2 → z ∈ O := by
  let S : Set ((LoopCircle × LoopCircle) × ℝ) :=
    {z | z.2 ∈ K ∧ rho ≤ dist z.1.1 z.1.2}
  have hS : IsCompact S := by
    have hbase : IsCompact ((univ : Set (LoopCircle × LoopCircle)) ×ˢ K) :=
      isCompact_univ.prod hK
    have hdist : IsClosed {z : (LoopCircle × LoopCircle) × ℝ |
        rho ≤ dist z.1.1 z.1.2} :=
      isClosed_le continuous_const (continuous_fst.fst.dist continuous_fst.snd)
    convert hbase.inter_right hdist using 1
    ext z
    simp only [S, mem_inter_iff, mem_prod, mem_univ, true_and, mem_ofPred_eq]
  have hcont := continuousOn_circle_family Gamma V J hV hJ hGamma
  have hevent : ∀ z ∈ S, ∀ᶠ w : P × ((LoopCircle × LoopCircle) × ℝ) in 𝓝 (0, z),
      Gamma w.1 w.2.2 w.2.1.1 = Gamma w.1 w.2.2 w.2.1.2 → w.2 ∈ O := by
    intro z hz
    by_cases hzo : z ∈ O
    · filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hO.mem_nhds hzo)] with w hw
      exact fun _ => hw
    · have hleft : ContinuousAt (fun w : P × ((LoopCircle × LoopCircle) × ℝ) =>
          Gamma w.1 w.2.2 w.2.1.1) (0, z) :=
        (hcont.continuousAt (((isOpen_univ.prod hV).prod hJ).mem_nhds
          ⟨⟨mem_univ _, hzero⟩, hKJ hz.1⟩)).comp
            ((continuous_snd.fst.fst.prodMk continuous_fst).prodMk continuous_snd.snd).continuousAt
      have hright : ContinuousAt (fun w : P × ((LoopCircle × LoopCircle) × ℝ) =>
          Gamma w.1 w.2.2 w.2.1.2) (0, z) :=
        (hcont.continuousAt (((isOpen_univ.prod hV).prod hJ).mem_nhds
          ⟨⟨mem_univ _, hzero⟩, hKJ hz.1⟩)).comp
            ((continuous_snd.fst.snd.prodMk continuous_fst).prodMk continuous_snd.snd).continuousAt
      have hne : Gamma 0 z.2 z.1.1 ≠ Gamma 0 z.2 z.1.2 :=
        fun h => hzo (hcover z hz.1 hz.2 h)
      filter_upwards [(hleft.ne_iff_eventually_ne hright).mp hne] with w hw
      exact fun h => (hw h).elim
  have hall := hS.eventually_forall_of_forall_eventually (x₀ := (0 : P))
    (P := fun p z => Gamma p z.2 z.1.1 = Gamma p z.2 z.1.2 → z ∈ O) hevent
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hV.mem_nhds hzero) hall)
  refine ⟨delta, hdelta, fun p hp => (hball hp).1, ?_⟩
  intro p hp z ht hsep heq
  exact (hball hp).2 z ⟨ht, hsep⟩ heq

end PoincareConjecture.M65Perturbation
