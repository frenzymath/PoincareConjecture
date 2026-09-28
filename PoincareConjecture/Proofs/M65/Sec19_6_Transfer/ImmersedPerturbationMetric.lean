import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationVelocity
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ}




theorem metric_pairing_contDiffOn (F : RicciFlow 3 M (Icc a b))
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ)))
    (hTime : ∀ z ∈ U, z.2.2 ∈ Icc a b)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (Y Z : (z : P × (ℝ × ℝ)) → TangentSpace (𝓡 3) (c z))
    (hY : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z, Y z⟩ : TangentBundle (𝓡 3) M)) U)
    (hZ : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z, Z z⟩ : TangentBundle (𝓡 3) M)) U) :
    ContDiffOn ℝ ∞ (fun z => (F.metric z.2.2).inner (c z) (Y z) (Z z)) U := by
  have ht : ContMDiff 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : P × (ℝ × ℝ) => z.2.2) := contDiff_snd.snd.contMDiff
  have hg := F.smooth.comp (ht.contMDiffOn.prodMk hc)
    (fun z hz => ⟨hTime z hz, mem_univ _⟩)
  suffices ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z => (F.metric z.2.2).inner (c z) (Y z) (Z z)) U from this.contDiffOn
  intro z hz
  have hp : ContMDiffWithinAt 𝓘(ℝ, P × (ℝ × ℝ)) ((𝓡 3).prod 𝓘(ℝ, ℝ)) ∞
      (fun w => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (c w)
        ((F.metric w.2.2).inner (c w) (Y w) (Z w))) U z :=
    (hg z hz).clm_bundle_apply₂ (hY z hz) (hZ z hz)
  exact (Bundle.contMDiffWithinAt_totalSpace.mp hp).2




theorem smul_field_contMDiffOn
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (v : P × (ℝ × ℝ) → ℝ) (hv : ContDiffOn ℝ ∞ v U)
    (Y : (z : P × (ℝ × ℝ)) → TangentSpace (𝓡 3) (c z))
    (hY : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z, Y z⟩ : TangentBundle (𝓡 3) M)) U) :
    ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z, v z • Y z⟩ : TangentBundle (𝓡 3) M)) U := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hc.contMDiffAt (hU.mem_nhds hz), ?_⟩
  have hcoord := (hv.contMDiffOn.contMDiffAt (hU.mem_nhds hz)).smul
    (Bundle.contMDiffAt_totalSpace.mp (hY.contMDiffAt (hU.mem_nhds hz))).2
  apply hcoord.congr_of_eventuallyEq
  let e := trivializationAt LoopAmbient (TangentSpace (𝓡 3)) (c z)
  have hnear : ∀ᶠ w in 𝓝 z, c w ∈ e.baseSet :=
    (hc.contMDiffAt (hU.mem_nhds hz)).continuousAt
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (c z)))
  filter_upwards [hnear] with w hw
  change (e ⟨c w, v w • Y w⟩).2 = v w • (e ⟨c w, Y w⟩).2
  simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hw] using
    (e.continuousLinearMapAt ℝ (c w)).map_smul (v w) (Y w)



theorem speed_contDiffOn (F : RicciFlow 3 M (Icc a b))
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hTime : ∀ z ∈ U, z.2.2 ∈ Icc a b)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (himm : ∀ z ∈ U,
      curveVelocity (n := 3) (fun x => c (z.1, (x, z.2.2))) z.2.1 ≠ 0) :
    ContDiffOn ℝ ∞
      (fun z => curveSpeed F (fun x t => c (z.1, (x, t))) z.2.2 z.2.1) U := by
  have hX := angular_velocity_contMDiffOn c U hU hc
  exact (metric_pairing_contDiffOn F c U hTime hc _ _ hX hX).sqrt
    (fun z hz => ((F.metric z.2.2).pos _ _ (himm z hz)).ne')




theorem unitTangent_contMDiffOn (F : RicciFlow 3 M (Icc a b))
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hTime : ∀ z ∈ U, z.2.2 ∈ Icc a b)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (himm : ∀ z ∈ U,
      curveVelocity (n := 3) (fun x => c (z.1, (x, z.2.2))) z.2.1 ≠ 0) :
    ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z,
        spatialUnitTangent F (fun x t => c (z.1, (x, t))) z.2.2 z.2.1⟩ :
          TangentBundle (𝓡 3) M)) U := by
  have hv := (speed_contDiffOn F c U hU hTime hc himm).inv
    (fun z hz => (Real.sqrt_pos.mpr ((F.metric z.2.2).pos _ _ (himm z hz))).ne')
  exact smul_field_contMDiffOn c U hU hc _ hv _
    (angular_velocity_contMDiffOn c U hU hc)

end PoincareConjecture.M65Perturbation
