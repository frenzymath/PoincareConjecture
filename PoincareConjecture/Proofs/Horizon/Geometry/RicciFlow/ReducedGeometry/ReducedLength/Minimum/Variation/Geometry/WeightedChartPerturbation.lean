import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartCurveExtension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def weightedChartPerturbation (p : M) (W : Set ℝ) (ρ : ℝ → ℝ)
    (B : ℝ → P →L[ℝ] E) (f : ℝ × P → M) (z : ℝ × P) : M := by
  classical
  exact if z.1 ∈ W ∧ f z ∈ (chartAt E p).source then
    (chartAt E p).symm ((chartAt E p) (f z) + ρ z.1 • B z.1 z.2) else f z

theorem weightedChartPerturbation_eq_of_zero (p : M) (W : Set ℝ) (ρ : ℝ → ℝ)
    (B : ℝ → P →L[ℝ] E) (f : ℝ × P → M) (z : ℝ × P)
    (hzero : ρ z.1 = 0 ∨ B z.1 z.2 = 0) :
    weightedChartPerturbation p W ρ B f z = f z := by
  classical
  unfold weightedChartPerturbation
  split_ifs with h
  · have hinc : ρ z.1 • B z.1 z.2 = 0 := by
      rcases hzero with hzero | hzero <;> simp only [hzero, zero_smul, smul_zero]
    rw [hinc, add_zero, (chartAt E p).left_inv h.2]
  · rfl

theorem weightedChartPerturbation_center (p : M) (W : Set ℝ) (ρ : ℝ → ℝ)
    (B : ℝ → P →L[ℝ] E) (f : ℝ × P → M) (s : ℝ) :
    weightedChartPerturbation p W ρ B f (s, 0) = f (s, 0) :=
  weightedChartPerturbation_eq_of_zero p W ρ B f (s, 0) (Or.inr (map_zero (B s)))

theorem weightedChartPerturbation_smooth_near_center
    (p : M) (W : Set ℝ) (hW : IsOpen W) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρW : tsupport ρ ⊆ W)
    (B : ℝ → P →L[ℝ] E) (hB : ContDiffOn ℝ ∞ B W)
    (f : ℝ × P → M) (U : Set (ℝ × P)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞ f U)
    (K : Set ℝ) (hK : ∀ s ∈ K, (s, (0 : P)) ∈ U)
    (hchart : ∀ s ∈ K ∩ tsupport ρ, f (s, 0) ∈ (chartAt E p).source) :
    ∃ V : Set (ℝ × P), IsOpen V ∧ V ⊆ U ∧
      (∀ s ∈ K, (s, (0 : P)) ∈ V) ∧
      ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞
        (weightedChartPerturbation p W ρ B f) V := by
  classical
  let e := chartAt E p
  let U0 := (U ∩ (W ×ˢ Set.univ)) ∩ f ⁻¹' e.source
  have hU0 : IsOpen U0 :=
    (hf.mono Set.inter_subset_left).continuousOn.isOpen_inter_preimage
      (hU.inter (hW.prod isOpen_univ)) e.open_source
  have hf0 : ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞ f U0 :=
    hf.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  let k : ℝ × P → E := fun z ↦ e (f z) + ρ z.1 • B z.1 z.2
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × P ↦ e (f z)) U0 :=
    (contMDiffOn_chart.comp hf0 (fun z hz ↦ hz.2)).contDiffOn
  have hBp : ContDiffOn ℝ ∞ (fun z : ℝ × P ↦ B z.1 z.2) U0 :=
    (hB.comp contDiffOn_fst (fun z hz ↦ hz.1.2.1)).clm_apply contDiffOn_snd
  have hk : ContDiffOn ℝ ∞ k U0 :=
    hc.add (((hρ.comp contDiff_fst).contDiffOn).smul hBp)
  let V0 := U ∩ ((tsupport ρ)ᶜ ×ˢ Set.univ)
  let V1 := U0 ∩ k ⁻¹' e.target
  have hV0 : IsOpen V0 := hU.inter ((isClosed_tsupport ρ).isOpen_compl.prod isOpen_univ)
  have hV1 : IsOpen V1 := hk.continuousOn.isOpen_inter_preimage hU0 e.open_target
  have hg0 : ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞
      (weightedChartPerturbation p W ρ B f) V0 := by
    apply (hf.mono Set.inter_subset_left).congr
    intro z hz
    exact weightedChartPerturbation_eq_of_zero p W ρ B f z
      (Or.inl (image_eq_zero_of_notMem_tsupport hz.2.1))
  have hg1 : ContMDiffOn (𝓘(ℝ, ℝ × P)) (𝓡 n) ∞
      (weightedChartPerturbation p W ρ B f) V1 := by
    have hcomp := (contMDiffOn_chart_symm (I := 𝓡 n) (x := p)).comp
      (hk.mono Set.inter_subset_left).contMDiffOn (fun z hz ↦ hz.2)
    apply hcomp.congr
    intro z hz
    exact if_pos (show z.1 ∈ W ∧ f z ∈ e.source from ⟨hz.1.1.2.1, hz.1.2⟩)
  refine ⟨V0 ∪ V1, hV0.union hV1, ?_, ?_, hg0.union_of_isOpen hg1 hV0 hV1⟩
  · intro z hz
    rcases hz with hz | hz
    · exact hz.1
    · exact hz.1.1.1
  · intro s hs
    by_cases hsupport : s ∈ tsupport ρ
    · apply Or.inr
      have hsc := hchart s ⟨hs, hsupport⟩
      refine ⟨⟨⟨hK s hs, hρW hsupport, Set.mem_univ _⟩, hsc⟩, ?_⟩
      change k (s, 0) ∈ e.target
      simpa only [k, map_zero, smul_zero, add_zero] using e.map_source hsc
    · exact Or.inl ⟨hK s hs, hsupport, Set.mem_univ _⟩

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
