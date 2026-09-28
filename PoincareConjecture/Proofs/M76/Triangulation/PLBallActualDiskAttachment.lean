import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels










set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]





theorem IsFinitePLBallPair.union_of_actual_disk_contact
    {B U S T d q : Set X}
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B S)
    (hU : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) U T)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hdS : d ⊆ S) (hdT : d ⊆ T)
    (hSout : (S \ d).Nonempty) (hTout : (T \ d).Nonempty)
    (hBU : B ∩ U = d) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B ∪ U)
      ((S \ (d \ q)) ∪ (T \ (d \ q))) := by
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  have hb := hB.boundary_disk_complement hdim hd hdS hSout
  have hc := hU.boundary_disk_complement hdim hd hdT hTout
  have hunion {s : Set X} (hds : d ⊆ s) : (s \ (d \ q)) ∪ d = s := by
    ext x
    have hx := @hds x
    change ((x ∈ s ∧ ¬ (x ∈ d ∧ x ∉ q)) ∨ x ∈ d) ↔ x ∈ s
    tauto
  have hinter {s : Set X} (hds : d ⊆ s) : (s \ (d \ q)) ∩ d = q := by
    ext x
    have hx := @hds x
    have hxq := @hd.1 x
    change ((x ∈ s ∧ ¬ (x ∈ d ∧ x ∉ q)) ∧ x ∈ d) ↔ x ∈ q
    tauto
  have hB' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B ((S \ (d \ q)) ∪ d) := by
    rwa [hunion hdS]
  have hU' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) U ((T \ (d \ q)) ∪ d) := by
    rwa [hunion hdT]
  exact hB'.union_of_ball_disk_attachment hU' hb hc hd (hinter hdS) (hinter hdT) hBU

end Set
