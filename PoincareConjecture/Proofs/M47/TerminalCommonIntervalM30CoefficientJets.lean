import PoincareConjecture.Proofs.M47.TerminalCommonIntervalM30Map
import PoincareConjecture.Proofs.M47.LimitCanonicalRoundCoefficientJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem terminalCommonInterval_m30_terminal_coefficients
    (n : ℕ) (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0)
    (q : G.limit.sliceCarrier.carrier) (x : E) :
    RiemannianMetric.pullbackCoefficients
      (M13.scaleSmoothMetric ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n)))
      (terminalCommonInterval_m30TerminalMap G n ∘ (extChartAt (𝓡 3) q).symm) x =
        limitNoncollapseChartForm (G.embedding n) q 0 h0 x := by
  have hmap := (terminalCommonInterval_m30_terminal_maps G n h0).1
  have hcoeff := congrArg (fun z : (t : ℝ) × (G.limit.sliceCarrier.carrier →
      ((V.flow (G.subsequence n)).slice t).carrier) =>
      V.scale (G.subsequence n) • ((V.flow (G.subsequence n)).metric z.1).pullbackCoefficients
        (z.2 ∘ (extChartAt (𝓡 3) q).symm) x) hmap
  calc
    _ = V.scale (G.subsequence n) •
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1).pullbackCoefficients
          (terminalCommonInterval_m30TerminalMap G n ∘ (extChartAt (𝓡 3) q).symm) x := by
      ext v w
      rfl
    _ = _ := hcoeff



theorem terminalCommonInterval_m30_terminal_coefficient_jets
    (P : M47Predecessors.{u}) (q : G.limit.sliceCarrier.carrier)
    (m : ℕ) {K : Set E} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m
        (RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric
          ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
          (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n)))
          (terminalCommonInterval_m30TerminalMap G n ∘ (extChartAt (𝓡 3) q).symm)))
      (iteratedFDeriv ℝ m ((G.limit.flow.metric 0).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm)) atTop K := by
  let c := extChartAt (𝓡 3) q
  have hconv := (limitCanonical_round_bilinear_coefficient_convergence P G q 0
    G.limit.zero_mem).jets m K hK hKc
  have himage : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm q).mono hKc)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset himage
  apply hconv.congr
  filter_upwards [eventually_ge_atTop j] with n hn x hx
  have hspace : c.symm '' K ⊆ G.exhaustion.space n :=
    hj.trans (G.exhaustion.space_increasing hn)
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos n).le, le_rfl⟩
  let W := c.target ∩ c.symm ⁻¹' G.exhaustion.space n
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) (G.exhaustion.space_open n)
  have hxW : x ∈ W := ⟨hKc hx, hspace (mem_image_of_mem c.symm hx)⟩
  have heq : (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)
      (fun a b : Fin 3 => blowupPullbackCoefficient (G.embedding n) q a b (0, y)))
      =ᶠ[𝓝 x] RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n)))
          (terminalCommonInterval_m30TerminalMap G n ∘ c.symm) := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact (limitCanonical_round_reconstructed_eq_chartForm (G.embedding n)
      (G.exhaustion.space_open n) q 0 h0 y hy.1 hy.2).trans
        (terminalCommonInterval_m30_terminal_coefficients G n h0 q y).symm
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

end PoincareConjecture.M47
