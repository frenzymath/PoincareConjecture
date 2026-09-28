import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedMetricLimit
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "basis" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance retainedBilinearNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance retainedBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem bilinear_jets_of_surgeryMetricLimitOn
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {V : Set A.carrier} {T : ℝ}
    (hlim : SurgeryMetricLimitOn A B g gT f V T)
    (q : A.carrier) (hq : q ∈ V) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hV : (extChartAt (𝓡 3) q).symm '' U ⊆ V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ (extChartAt (𝓡 3) q).symm) U)
    (k : ℕ) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, T - d < t → t < T → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k ((g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm) x -
        iteratedFDeriv ℝ k (gT.pullbackCoefficients
          (f ∘ (extChartAt (𝓡 3) q).symm)) x‖ < eta := by
  classical
  have hsmall : 0 < eta / 10 := div_pos heta (by norm_num)
  have hKV : (extChartAt (𝓡 3) q).symm '' K ⊆ V := (image_mono hKU).trans hV
  choose d hd hbound using fun i j : Fin 3 =>
    hlim q hq K hK (hKU.trans hchart) hKV k i j (eta / 10) hsmall
  let delta := Finset.univ.inf' Finset.univ_nonempty
    (fun p : Fin 3 × Fin 3 => d p.1 p.2)
  have hdelta : 0 < delta :=
    (Finset.lt_inf'_iff _).mpr (fun p _ => hd p.1 p.2)
  have hle (i j : Fin 3) : delta ≤ d i j :=
    Finset.inf'_le _ (Finset.mem_univ (i, j))
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hT x hx
  have hc := ((g t).contDiffOn_chartCoefficients q).contDiffAt
    ((isOpen_extChartAt_target q).mem_nhds (hchart (hKU hx)))
  have hf' := gT.contDiffAt_pullbackCoefficients (hf.contMDiffAt (hU.mem_nhds (hKU hx)))
  have hk : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [← iteratedFDeriv_sub_apply (hc.of_le hk) (hf'.of_le hk)]
  have hcomponents (i j : Fin 3) :
      ‖iteratedFDeriv ℝ k (fun y =>
        (((g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm -
          gT.pullbackCoefficients (f ∘ (extChartAt (𝓡 3) q).symm)) y) (basis i) (basis j))
        x‖ ≤ eta / 10 := by
    have hc' := (hc.clm_apply (contDiffAt_const (c := basis i))).clm_apply
      (contDiffAt_const (c := basis j))
    have hf'' := (hf'.clm_apply (contDiffAt_const (c := basis i))).clm_apply
      (contDiffAt_const (c := basis j))
    change ‖iteratedFDeriv ℝ k (fun y =>
      ((g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm y) (basis i) (basis j) -
        (gT.pullbackCoefficients (f ∘ (extChartAt (𝓡 3) q).symm) y)
          (basis i) (basis j)) x‖ ≤ eta / 10
    rw [fun_iteratedFDeriv_sub_apply (hc'.of_le hk) (hf''.of_le hk)]
    exact (hbound i j t (by linarith [hle i j]) hT x hx).le
  have hnorm := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components
    basis (hc.sub hf') k hcomponents
  exact hnorm.trans_lt (by norm_num; linarith)

theorem retained_bilinear_jet_limit
    {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (event : SurgeryEventData g0 K P slice metric T)
    (q : (slice event.tMinus).carrier) (hq : q ∈ interior event.retained_pre)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre)
    (k : ℕ) {L : Set E} (hL : IsCompact L) (hLU : L ⊆ U)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, T - d < t → t < T → ∀ x ∈ L,
      ‖iteratedFDeriv ℝ k
          ((event.pre_flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm) x -
        iteratedFDeriv ℝ k ((metric T).pullbackCoefficients
          (event.retention.map ∘ (extChartAt (𝓡 3) q).symm)) x‖ < eta := by
  apply bilinear_jets_of_surgeryMetricLimitOn (metric_converges_retention event)
    q hq hU hchart hret _ k hL hLU heta
  exact (event.retention.map_smooth.mono interior_subset).comp
    ((contMDiffOn_extChartAt_symm q).mono hchart)
    (fun x hx => hret (mem_image_of_mem _ hx))

end PoincareConjecture.M44
