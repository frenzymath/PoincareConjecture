import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderBuffer
import PoincareConjecture.Proofs.M47.SeedCylinderClock









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {T epsilon : ℝ}
  (N : SurgeryStrongNeck F T epsilon)

private theorem physicalClock_mem :
    MapsTo (fun s : ℝ => (N.neck.scale⁻¹ ^ 2) * s)
      (Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) (Ioc (-1 : ℝ) 0) := by
  intro s hs
  have hQ := N.cylinder.scale_pos
  constructor
  · have h := mul_lt_mul_of_pos_left hs.1 hQ
    simpa only [mul_neg, mul_inv_cancel₀ hQ.ne'] using h
  · exact mul_nonpos_of_nonneg_of_nonpos hQ.le hs.2

private theorem physicalClock_mono :
    StrictMonoOn (fun s : ℝ => (N.neck.scale⁻¹ ^ 2) * s)
      (Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) :=
  fun _ _ _ _ hst => mul_lt_mul_of_pos_left hst N.cylinder.scale_pos

private theorem physicalClock_time (s : ℝ)
    (_hs : s ∈ Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) :
    T + s / 1 = T + ((N.neck.scale⁻¹ ^ 2) * s) / (N.neck.scale⁻¹ ^ 2) := by
  simp only [div_one, mul_div_cancel_left₀ s N.cylinder.scale_pos.ne']



noncomputable def strongNeckPhysicalClock :
    SurgeryFlowCylinder F (F.slice T) T 1
      (Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) N.neck.carrier :=
  seedCylinderReclock N.cylinder (by norm_num : (0 : ℝ) < 1) ordConnected_Ioc
    (fun s : ℝ => (N.neck.scale⁻¹ ^ 2) * s)
    (physicalClock_mem N) (physicalClock_mono N) (physicalClock_time N)



theorem strongNeckPhysicalClock_parameter {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0) :
    s / (N.neck.scale⁻¹ ^ 2) ∈ Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0 := by
  constructor
  · simpa only [neg_div, one_div] using
      (div_lt_div_iff_of_pos_right N.cylinder.scale_pos).mpr hs.1
  · exact div_nonpos_of_nonpos_of_nonneg hs.2 N.cylinder.scale_pos.le



theorem strongNeckPhysicalClock_forward (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0)
    (x : (F.slice T).carrier) :
    HEq ((strongNeckPhysicalClock N).forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x)
      (N.cylinder.forward s hs x) := by
  have hf := seedCylinderReclock_forward_heq N.cylinder
    (by norm_num : (0 : ℝ) < 1) ordConnected_Ioc
    (fun t : ℝ => (N.neck.scale⁻¹ ^ 2) * t)
    (physicalClock_mem N) (physicalClock_mono N) (physicalClock_time N)
    (s / (N.neck.scale⁻¹ ^ 2)) hs' x
  have heq : ∀ t (ht : t ∈ Ioc (-1 : ℝ) 0), t = s →
      HEq (N.cylinder.forward t ht x) (N.cylinder.forward s hs x) := by
    intro t ht hts
    subst t
    rfl
  exact hf.trans (heq _ _ (mul_div_cancel₀ s N.cylinder.scale_pos.ne'))



theorem strongNeckPhysicalClock_terminal
    (hs : (0 : ℝ) ∈ Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0)
    (x : (F.slice T).carrier) (hx : x ∈ N.neck.carrier) :
    HEq ((strongNeckPhysicalClock N).forward 0 hs x) x := by
  have hf := seedCylinderReclock_forward_heq N.cylinder
    (by norm_num : (0 : ℝ) < 1) ordConnected_Ioc
    (fun t : ℝ => (N.neck.scale⁻¹ ^ 2) * t)
    (physicalClock_mem N) (physicalClock_mono N) (physicalClock_time N) 0 hs x
  have heq : ∀ t (ht : t ∈ Ioc (-1 : ℝ) 0), t = 0 →
      HEq (N.cylinder.forward t ht x) x := by
    intro t ht ht0
    subst t
    exact N.terminal_identity ht x hx
  exact hf.trans (heq _ _ (mul_zero _))

end PoincareConjecture.Proofs.M47
