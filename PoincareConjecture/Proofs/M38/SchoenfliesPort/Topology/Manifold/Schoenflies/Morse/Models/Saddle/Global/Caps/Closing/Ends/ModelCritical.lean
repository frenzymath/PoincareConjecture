import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.Minimum

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_critical_in_terminal_model_cap
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    ∃ q ∈ data.toTerminalSaddleGeometry.modelDomain i,
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) ∉
        data.toTerminalSaddleGeometry.I ∧
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y : S2 => inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel y)) q = 0 := by
  let : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2
  let h : S2 → Real := fun q =>
    inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q)
  let O : Set S2 := {q | h q ∉ data.toTerminalSaddleGeometry.I}
  let K := data.toTerminalSaddleGeometry.modelDomain i
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp contMDiff_coe_sphere)
  have hO : IsOpen O :=
    (isClosed_Icc.preimage hh.continuous).isOpen_compl
  have hK : IsCompact K := by
    have hc : IsCompact (data.modelDisk i '' closedBall (0 : E2) 1) :=
      (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
        ((data.modelDisk i).continuousOn.mono (data.modelDisk_source i))
    rw [data.modelDisk_image] at hc
    exact hc
  have hseed : data.modelSeed i ∈ O := data.modelSeed_outside i
  have hseedK : data.modelSeed i ∈ K :=
    subset_closure (mem_connectedComponentIn hseed)
  have hnhds (q : S2) (hq : q ∈ K) (hqO : q ∈ O) : K ∈ 𝓝 q := by
    have hV := hO.connectedComponentIn (x := q)
    have hqV := mem_connectedComponentIn hqO
    obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hq _ hV hqV
    have hzq := connectedComponentIn_eq hzV
    have hzs := connectedComponentIn_eq hzC
    have hqC : q ∈ connectedComponentIn O (data.modelSeed i) := by
      rw [hzs, ← hzq]
      exact hqV
    exact mem_of_superset (hO.connectedComponentIn.mem_nhds hqC) subset_closure
  have hsplit : h (data.modelSeed i) < data.ends.lowerCut ∨
      data.ends.upperCut < h (data.modelSeed i) := by
    change ¬ (_ ≤ _ ∧ _ ≤ _) at hseed
    simpa only [not_and_or, not_le] using hseed
  rcases hsplit with hbelow | habove
  · obtain ⟨q, hqK, hmin⟩ := hK.exists_isMinOn ⟨data.modelSeed i, hseedK⟩
      hh.continuous.continuousOn
    have hqO : q ∈ O := by
      exact fun hc => (not_le_of_gt ((hmin hseedK).trans_lt hbelow)) hc.1
    refine ⟨q, hqK, hqO, ?_⟩
    exact Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh
      (hmin.isLocalMin (hnhds q hqK hqO))
  · obtain ⟨q, hqK, hmax⟩ := hK.exists_isMaxOn ⟨data.modelSeed i, hseedK⟩
      hh.continuous.continuousOn
    have hqO : q ∈ O := by
      exact fun hc => (not_le_of_gt (habove.trans_le (hmax hseedK))) hc.2
    refine ⟨q, hqK, hqO, ?_⟩
    have hn := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh.neg
      (hmax.isLocalMax (hnhds q hqK hqO)).neg
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q = 0 at hn
    simpa only [mfderiv_neg, neg_eq_zero] using hn

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
