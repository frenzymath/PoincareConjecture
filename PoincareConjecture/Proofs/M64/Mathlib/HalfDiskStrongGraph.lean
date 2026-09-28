import PoincareConjecture.Proofs.M64.Mathlib.HalfDiskPolarRepresentatives
import PoincareConjecture.Proofs.M64.Mathlib.RestrictedPullbackLp














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture

open Proofs.M58

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ

private theorem continuous_compact_memLp {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] {mu : Measure X}
    [IsFiniteMeasureOnCompacts mu] {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : Continuous f) : MemLp f 2 (mu.restrict K) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact hK)






theorem m64HalfDisk_strong_graph_extract {epsilon R H : ℝ}
    (hepsilon : 0 < epsilon) (hRH : R ≤ H)
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ)
    (hu : MemLp u 2 (volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (hV : ∀ i, MemLp (V i) 2
      (volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (hb : MemLp b 2 (volume.restrict (Icc (-H) H)))
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hval : Tendsto (fun j => eLpNorm (f j - u) 2
      (volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}))) atTop (𝓝 0))
    (hcol : ∀ i : Fin 2, Tendsto (fun j => eLpNorm
      (fun z => fderiv ℝ (f j) z (basis i) - V i z) 2
        (volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}))) atTop (𝓝 0))
    (htrace : Tendsto (fun j => eLpNorm (fun s => f j (s • basis 0) - b s)
      2 (volume.restrict (Icc (-H) H))) atTop (𝓝 0)) :
    ∀ᵐ r ∂volume.restrict (Icc epsilon R),
      MemLp (fun theta => u (r • angularPoint theta))
        2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
        (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
          V i z * test z + u z * fderiv ℝ test z (basis i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            u (r • angularPoint theta) * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r, b s * test (s • basis 0)) ∧
      MemLp (fun theta => -r * Real.sin theta * V 0 (r • angularPoint theta) +
        r * Real.cos theta * V 1 (r • angularPoint theta))
          2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
          fun theta => u (r • angularPoint theta)) ∧
        v 0 = b r ∧ v Real.pi = b (-r) ∧
        ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ theta in s..t,
            -r * Real.sin theta * V 0 (r • angularPoint theta) +
              r * Real.cos theta * V 1 (r • angularPoint theta) := by
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  let mu := volume.restrict K
  let nu := volume.restrict (Icc (-H) H)
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) H).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hfm (j : ℕ) : MemLp (f j) 2 mu := continuous_compact_memLp hK (hf j).continuous
  have hDm (j : ℕ) (i : Fin 2) : MemLp (fun z => fderiv ℝ (f j) z (basis i)) 2 mu :=
    continuous_compact_memLp hK
      (((hf j).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hBm (j : ℕ) : MemLp (fun s => f j (s • basis 0)) 2 nu :=
    continuous_compact_memLp isCompact_Icc
      ((hf j).continuous.comp (continuous_id.smul continuous_const))
  let A := fun j => (hfm j).toLp (f j)
  let W := fun j i => (hDm j i).toLp (fun z => fderiv ℝ (f j) z (basis i))
  let B := fun j => (hBm j).toLp (fun s => f j (s • basis 0))
  let U := hu.toLp u
  let D := fun i => (hV i).toLp (V i)
  let beta := hb.toLp b
  have hAU : Tendsto A atTop (𝓝 U) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfm u hu).mpr hval
  have hWD (i : Fin 2) : Tendsto (fun j => W j i) atTop (𝓝 (D i)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun j z => fderiv ℝ (f j) z (basis i)) (fun j => hDm j i) (V i) (hV i)).mpr (hcol i)
  have hBb : Tendsto B atTop (𝓝 beta) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun j s => f j (s • basis 0)) hBm b hb).mpr htrace
  have hgreen := M65Boundary.halfDisk_graph_green hepsilon hRH f hf A W U D B beta
    (fun j => (hfm j).coeFn_toLp) (fun j i => (hDm j i).coeFn_toLp)
    (fun j => (hBm j).coeFn_toLp) hAU hWD hBb
  have hac := M65Boundary.halfDisk_graph_AC hepsilon hRH f hf A W U D B beta
    (fun j => (hfm j).coeFn_toLp) (fun j i => (hDm j i).coeFn_toLp)
    (fun j => (hBm j).coeFn_toLp) hAU hWD hBb
  have huarc := m64HalfDisk_polar_ae hepsilon hRH hu.coeFn_toLp
  have hdarc (i : Fin 2) := m64HalfDisk_polar_ae hepsilon hRH (hV i).coeFn_toLp
  have hmem : ∀ᵐ r ∂volume.restrict (Icc epsilon R), r ∈ Icc (-H) H ∧ -r ∈ Icc (-H) H := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hr0 := hepsilon.trans_le hr.1
    have hrH := hr.2.trans hRH
    exact ⟨⟨by linarith, hrH⟩, by constructor <;> linarith⟩
  have hbpos := m64MeasurePreserving_ae_restrict (MeasurePreserving.id volume)
    measurableSet_Icc (hmem.mono fun _ h => h.1) hb.coeFn_toLp
  have hbneg := m64MeasurePreserving_ae_restrict (Measure.measurePreserving_neg volume)
    measurableSet_Icc (hmem.mono fun _ h => h.2) hb.coeFn_toLp
  filter_upwards [hgreen, hac, huarc, hdarc 0, hdarc 1, hbpos, hbneg,
    ae_restrict_mem measurableSet_Icc] with r hgr har huar hd0 hd1 hbpr hbnr hr
  have hr0 : 0 < r := hepsilon.trans_le hr.1
  have hrH : r ≤ H := hr.2.trans hRH
  have hKrK : closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} ⊆ K :=
    inter_subset_inter (closedBall_subset_closedBall hrH) Subset.rfl
  have hdtheta : (fun theta => -r * Real.sin theta * D 0 (r • angularPoint theta) +
      r * Real.cos theta * D 1 (r • angularPoint theta))
      =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)] fun theta =>
        -r * Real.sin theta * V 0 (r • angularPoint theta) +
          r * Real.cos theta * V 1 (r • angularPoint theta) := by
    filter_upwards [hd0, hd1] with theta h0 h1
    rw [h0, h1]
  refine ⟨hgr.1.ae_eq huar, ?_, har.1.ae_eq hdtheta, ?_⟩
  · intro test i
    have hl : (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        D i z * test z + U z * fderiv ℝ test z (basis i)) =
        ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
          V i z * test z + u z * fderiv ℝ test z (basis i) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hKrK hu.coeFn_toLp,
        ae_restrict_of_ae_restrict_of_subset hKrK (hV i).coeFn_toLp] with z hz hzi
      rw [hz, hzi]
    have hs : (∫ theta in (0 : ℝ)..Real.pi,
        U (r • angularPoint theta) * test (r • angularPoint theta) * angularPoint theta i) =
        ∫ theta in (0 : ℝ)..Real.pi,
          u (r • angularPoint theta) * test (r • angularPoint theta) * angularPoint theta i := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (uIoc_subset_uIcc.trans (uIcc_subset_Icc
          ⟨le_rfl, Real.pi_pos.le⟩ ⟨Real.pi_pos.le, le_rfl⟩)) huar] with theta htheta
      rw [htheta]
    have hbint : (∫ s in (-r)..r, beta s * test (s • basis 0)) =
        ∫ s in (-r)..r, b s * test (s • basis 0) := by
      apply intervalIntegral.integral_congr_ae_restrict
      have hsub : uIoc (-r) r ⊆ Icc (-H) H :=
        uIoc_subset_uIcc.trans (uIcc_subset_Icc
          ⟨by linarith, by linarith⟩ ⟨by linarith, hrH⟩)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hb.coeFn_toLp] with s hs
      rw [hs]
    simpa only [hl, hs, hbint] using hgr.2 test i
  · obtain ⟨v, hv, hvU, hv0, hvpi, hinc⟩ := har.2
    refine ⟨v, hv, hvU.trans huar, hv0.trans hbpr, hvpi.trans hbnr, ?_⟩
    intro s hs t ht
    rw [hinc s hs t ht]
    apply intervalIntegral.integral_congr_ae_restrict
    exact ae_restrict_of_ae_restrict_of_subset
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)) hdtheta

end PoincareConjecture
