import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds
import Mathlib.Topology.UniformSpace.HeineCantor











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 500000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)





theorem tendstoUniformlyOn_scalarNormalized_spatialJets
    (F : RicciFlow n M (Iic 0))
    {U : Set E} (hU : IsOpen U) {f : E → M}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {r : ℝ} (hr : 0 < r) {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} (hs : Tendsto s l (𝓝 r)) (m : ℕ) :
    TendstoUniformlyOn
      (fun k (z : ℝ × E) => iteratedFDeriv ℝ m
        (fun x => s k • (F.metric (z.1 / s k)).pullbackCoefficients f x) z.2)
      (fun z => iteratedFDeriv ℝ m
        (fun x => r • (F.metric (z.1 / r)).pullbackCoefficients f x) z.2)
      l (Icc (-1 : ℝ) 0 ×ˢ K) := by
  let A : Set ℝ := Icc (r / 2) (2 * r)
  let V : Set (ℝ × E) := Icc (-1 : ℝ) 0 ×ˢ K
  let B := fun (a : ℝ) (z : ℝ × E) => a •
    iteratedFDeriv ℝ m ((F.metric (z.1 / a)).pullbackCoefficients f) z.2
  have hapos {a : ℝ} (ha : a ∈ A) : 0 < a := (half_pos hr).trans_le ha.1
  have hjoint : ContinuousOn
      (fun z : ℝ × E => iteratedFDeriv ℝ m
        ((F.metric z.1).pullbackCoefficients f) z.2) (Iic 0 ×ˢ U) :=
    (SpacetimeBounds.contDiffOn_spatialJet_within
      (F.contDiffOn_pullbackCoefficients_within hU hf) (uniqueDiffOn_Iic 0) hU m).continuousOn
  have hcontinuous : ContinuousOn (fun p : ℝ × (ℝ × E) => B p.1 p.2) (A ×ˢ V) := by
    have hscale : ContinuousOn (fun p : ℝ × (ℝ × E) => p.1) (A ×ˢ V) :=
      continuous_fst.continuousOn
    have htime : ContinuousOn (fun p : ℝ × (ℝ × E) => (p.2.1 / p.1, p.2.2))
        (A ×ˢ V) :=
      ((continuousOn_snd.fst.div continuousOn_fst
        (fun p hp => (hapos hp.1).ne')).prodMk continuousOn_snd.snd)
    have hcomp := hjoint.comp htime (fun p hp =>
      ⟨div_nonpos_of_nonpos_of_nonneg hp.2.1.2 (hapos hp.1).le, hKU hp.2.2⟩)
    exact hscale.smul hcomp
  have hcompact : IsCompact (A ×ˢ V) := isCompact_Icc.prod (isCompact_Icc.prod hK)
  have hrA : r ∈ A := by constructor <;> linarith
  have hAn : A ∈ 𝓝 r := Icc_mem_nhds (by linarith) (by linarith)
  have huniform : TendstoUniformlyOn B (B r) (𝓝[A] r) V :=
    UniformContinuousOn.tendstoUniformlyOn (F := B)
      (hcompact.uniformContinuousOn_of_continuous hcontinuous) hrA
  rw [nhdsWithin_eq_nhds.mpr hAn] at huniform
  have hraw : TendstoUniformlyOn (fun k => B (s k)) (B r) l V :=
    fun W hW => hs.eventually (huniform W hW)
  have hjet (a : ℝ) (z : ℝ × E) (hz : z ∈ V) :
      iteratedFDeriv ℝ m
        (fun x => a • (F.metric (z.1 / a)).pullbackCoefficients f x) z.2 = B a z := by
    exact iteratedFDeriv_const_smul_apply'
      (((F.metric (z.1 / a)).contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds (hKU hz.2)))).of_le
          (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)))
  exact (hraw.congr (Eventually.of_forall fun k z hz => (hjet (s k) z hz).symm)).congr_right
    (fun z hz => (hjet r z hz).symm)

end PoincareConjecture.RicciFlow
