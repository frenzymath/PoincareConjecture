import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationInverse

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M65Perturbation

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

set_option maxHeartbeats 600000 in

theorem exists_zero_chart (Q : ((E × P) × E) → E) (w : (E × P) × E)
    (hQ : ContDiffAt ℝ 1 Q w) (hw : Q w = 0)
    (hblock : Function.Bijective (fun u : E => fderiv ℝ Q w ((u, 0), 0))) :
    ∃ (U : Set (E × P)) (W : Set ((E × P) × E)) (phi : (E × P) → ((E × P) × E)),
      IsOpen U ∧ IsOpen W ∧ w ∈ W ∧ ContDiffOn ℝ 1 phi U ∧
      (∀ v ∈ U, Q (phi v) = 0 ∧ ((phi v).2, (phi v).1.2) = v) ∧
      (∀ z ∈ W, Q z = 0 → (z.2, z.1.2) ∈ U ∧ phi (z.2, z.1.2) = z) := by
  obtain ⟨e, hwe, he, hinv⟩ := exists_augmented_inverse Q w hQ hblock
  obtain ⟨O, hO, heO⟩ := hinv.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVO, hV, hwV⟩ := mem_nhds_iff.mp hO
  let chi : E × P → E × (P × E) := fun v => (0, v.2, v.1)
  let sigma : ((E × P) × E) → E × P := fun z => (z.2, z.1.2)
  have hchi : ContDiff ℝ 1 chi :=
    contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst)
  have hsigma : Continuous sigma := continuous_snd.prodMk continuous_fst.snd
  let U := chi ⁻¹' (e.target ∩ V)
  let W := e.source ∩ sigma ⁻¹' U
  let phi : E × P → ((E × P) × E) := fun v => e.symm (chi v)
  have hU : IsOpen U := (e.open_target.inter hV).preimage hchi.continuous
  have hW : IsOpen W := e.open_source.inter (hU.preimage hsigma)
  have hbase : chi (sigma w) = e w := by
    rw [he, hw]
  have hwW : w ∈ W := by
    refine ⟨hwe, ?_⟩
    change chi (sigma w) ∈ e.target ∩ V
    rw [hbase]
    exact ⟨e.map_source hwe, hwV⟩
  have hphi : ContDiffOn ℝ 1 phi U :=
    heO.comp hchi.contDiffOn (fun _ hv => hVO hv.2)
  refine ⟨U, W, phi, hU, hW, hwW, hphi, ?_, ?_⟩
  · intro v hv
    have hephi : e (phi v) = chi v := e.right_inv hv.1
    have hfirst := congrArg Prod.fst hephi
    have htail := congrArg (fun z : E × (P × E) => (z.2.2, z.2.1)) hephi
    rw [he] at hfirst htail
    exact ⟨hfirst, htail⟩
  · intro z hz hQz
    refine ⟨hz.2, ?_⟩
    have hzero : chi (sigma z) = e z := by
      rw [he, hQz]
    change e.symm (chi (sigma z)) = z
    rw [hzero]
    exact e.left_inv hz.1

end PoincareConjecture.M65Perturbation
