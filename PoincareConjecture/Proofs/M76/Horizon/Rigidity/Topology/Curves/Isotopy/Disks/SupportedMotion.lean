import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.BodyIsotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.Tracks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization



set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

theorem continuous_family_of_joint_finitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (H : I → S ≃ₜ S) (f : (ℝ × E) → E)
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1 ×ˢ S))
    (hvalue : ∀ t : I, ∀ x : S, f ((t : ℝ), x) = (H t x : E)) :
    Continuous (fun z : I × S => H z.1 z.2) := by
  apply IsEmbedding.subtypeVal.continuous_iff.mpr
  have h := hf.continuousOn.domRestrict.comp
    (Homeomorph.Set.prod (Icc (0 : ℝ) 1) S).symm.continuous
  exact h.congr (fun z => hvalue z.1 z.2)

end PoincareConjecture.M76.CollarIsotopy

namespace Set

theorem IsFinitePLBallPair.exists_joint_PL_isotopy
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hs : IsFinitePLBallPair V S Q)
    (e : S ≃ₜ S) (he : e.IsFinitePL)
    (hfix : ∀ x : S, (x : E) ∈ Q → e x = x) :
    ∃ (H : I → S ≃ₜ S) (F Fi : (ℝ × E) → E),
      H 0 = Homeomorph.refl S ∧ H 1 = e ∧
      (∀ t : I, ∀ x : S, (x : E) ∈ Q → H t x = x) ∧
      Continuous (fun z : I × S => H z.1 z.2) ∧
      Continuous (fun z : I × S => (H z.1).symm z.2) ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ S) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ S) ∧
      (∀ t : I, ∀ x : S, F ((t : ℝ), x) = (H t x : E)) ∧
      (∀ t : I, ∀ x : S, Fi ((t : ℝ), x) = ((H t).symm x : E)) := by
  let n := Module.finrank ℝ V
  have hn : 0 < n := Module.finrank_pos
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let c : V ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  obtain ⟨q, hq, hqb⟩ := hs.exists_cube_chart c
  let C := Metric.closedBall (0 : Fin n → ℝ) 1
  let ec : C ≃ₜ C := q.symm.trans (e.trans q)
  have hec : ec.IsFinitePL := hq.symm.trans (he.trans hq)
  have hfixc (x : C) (hx : (x : Fin n → ℝ) ∈ frontier C) : ec x = x := by
    change q (e (q.symm x)) = x
    have hbd : (q.symm x : E) ∈ Q := (hqb (q.symm x)).mpr (by
      simpa only [q.apply_symm_apply] using hx)
    rw [hfix _ hbd, q.apply_symm_apply]
  obtain ⟨J, f, fi, hzero, hone, hfixed, hf, hfi, hfv, hfiv⟩ :=
    hec.exists_unit_halfspace_body_joint_PL_isotopy hfixc
      signedCubeCoordinate signedCubeCoordinate_ne_zero closedBall_eq_signedCube_halfspaces
  let H : I → S ≃ₜ S := fun t => q.trans ((J t).trans q.symm)
  obtain ⟨F, hF, hFv⟩ := PoincareConjecture.M76.CollarIsotopy.exists_conjugate_joint_finitePL
    q.symm hq.symm J f hf hfv
  obtain ⟨Fi, hFi, hFiv⟩ := PoincareConjecture.M76.CollarIsotopy.exists_conjugate_joint_finitePL
    q.symm hq.symm (fun t => (J t).symm) fi hfi hfiv
  have hval (t : I) (x : S) : F ((t : ℝ), x) = (H t x : E) := hFv t x
  have hival (t : I) (x : S) : Fi ((t : ℝ), x) = ((H t).symm x : E) := hFiv t x
  refine ⟨H, F, Fi, ?_, ?_, ?_,
    PoincareConjecture.M76.CollarIsotopy.continuous_family_of_joint_finitePL H F hF hval,
    PoincareConjecture.M76.CollarIsotopy.continuous_family_of_joint_finitePL
      (fun t => (H t).symm) Fi hFi hival, hF, hFi, hval, hival⟩
  · apply Homeomorph.ext
    intro x
    change q.symm (J 0 (q x)) = x
    rw [hzero]
    exact q.symm_apply_apply x
  · apply Homeomorph.ext
    intro x
    change q.symm (J 1 (q x)) = e x
    rw [hone]
    change q.symm (q (e (q.symm (q x)))) = e x
    rw [q.symm_apply_apply, q.symm_apply_apply]
  · intro t x hx
    change q.symm (J t (q x)) = x
    rw [hfixed t (q x) ((hqb x).mp hx), q.symm_apply_apply]

end Set
