import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNeighborhood

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D.SurgeryCapTag

local notation "I2" => (modelWithCornersSelf Real E2)
local notation "CINF" => ((Top.top : ENat) : WithTop ENat)

variable {psi psiNew : Prod UnitTwoSphere Real -> E3} {u : UnitTwoSphere}

theorem flatChart_mem_sourceCap (C : SurgeryCapTag psi u)
    (x : E2) (hx : norm x <= 1 / 4) : C.sourceCap (C.flatChart x) := by
  have hr : 0 <= 1 - norm x ^ 2 := by nlinarith [norm_nonneg x]
  let v : E3 := heightCoordinates.symm (x, -Real.sqrt (1 - norm x ^ 2))
  have hv : norm v = 1 := by
    have hv2 : norm v ^ 2 = 1 := by
      dsimp only [v]
      rw [heightCoordinates_symm_norm_sq, neg_sq, Real.sq_sqrt hr]
      ring
    nlinarith [norm_nonneg v]
  let q : UnitTwoSphere := { val := v, property := mem_sphere_zero_iff_norm.mpr hv }
  have hcoords : heightCoordinates (q : E3) = (x, -Real.sqrt (1 - norm x ^ 2)) :=
    heightCoordinates.apply_symm_apply _
  have hq : (heightCoordinates (q : E3)).2 <= 0 := by
    rw [hcoords]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  refine Exists.intro q (And.intro hq ?_)
  have hflat := C.flat_eq q hq (by rw [hcoords]; exact hx)
  simpa only [hcoords] using hflat.symm

theorem exists_source_band_mem (C : SurgeryCapTag psi u)
    (U : Set UnitTwoSphere) (hU : IsOpen U) (hcap : Set.Subset C.sourceCap U) :
    Exists fun d : Real => And (0 < d) (And (d <= C.overlapWidth)
      (forall q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < d ->
        And (C.sourceChart.source q) (U (C.sourceChart q)))) := by
  classical
  let V : Set UnitTwoSphere := {q | And (C.sourceChart.source q) (U (C.sourceChart q))}
  have hV : IsOpen V := C.sourceChart.isOpen_inter_preimage hU
  have hh : Continuous (fun q : UnitTwoSphere => -(heightCoordinates (q : E3)).2) :=
    ((heightCoordinates.continuous.comp continuous_subtype_val).snd).neg
  have hzero : Set.Subset {q : UnitTwoSphere | 0 <= -(heightCoordinates (q : E3)).2} V := by
    intro q hq
    change 0 <= -(heightCoordinates (q : E3)).2 at hq
    have hqs : (heightCoordinates (q : E3)).2 <= 0 := by linarith
    exact And.intro (C.south_mem_source q hqs)
      (hcap (Exists.intro q (And.intro hqs rfl)))
  have hex := exists_uniform_upper_level_band
    (fun q : UnitTwoSphere => -(heightCoordinates (q : E3)).2) hh hV hzero
  let d := Classical.choose hex
  have hd := Classical.choose_spec hex
  refine Exists.intro (min d C.overlapWidth)
    (And.intro (lt_min hd.1 C.overlap_pos) (And.intro (min_le_right _ _) ?_))
  intro q hq
  apply hd.2 q
  have hqd : (heightCoordinates (q : E3)).2 < d :=
    lt_of_lt_of_le hq (min_le_left _ _)
  linarith

noncomputable def pullback (C : SurgeryCapTag psi u)
    (e : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere)
    (he : ContMDiffOn I2 I2 CINF e e.source)
    (hei : ContMDiffOn I2 I2 CINF e.symm e.target)
    (gamma : Real) (hgamma : Ne gamma 0)
    (hcap : Set.Subset C.sourceCap e.target)
    (heq : forall p : UnitTwoSphere, e.source p -> forall s : Real, abs s < 1 ->
      psiNew (p, s) = psi (e p, gamma * s)) : SurgeryCapTag psiNew u := by
  classical
  let hex := C.exists_source_band_mem e.target e.open_target hcap
  let d := Classical.choose hex
  have hd := Classical.choose_spec hex
  refine {
    profile := C.profile
    cutHeight := C.cutHeight
    removal := C.removal
    scale := C.scale
    sign := C.sign
    removal_pos := C.removal_pos
    scale_pos := C.scale_pos
    sign_abs := C.sign_abs
    scale_small := C.scale_small
    tube := C.tube
    tube_source := C.tube_source
    tube_smooth := C.tube_smooth
    tube_inverse := C.tube_inverse
    tube_height := C.tube_height
    sourceChart := C.sourceChart.trans e.symm
    source_smooth := hei.comp (C.source_smooth.mono inter_subset_left) (fun _ hq => hq.2)
    source_inverse := C.source_inverse.comp (he.mono inter_subset_left) (fun _ hq => hq.2)
    overlapWidth := d
    overlap_pos := hd.1
    overlap_le := le_trans hd.2.1 C.overlap_le
    source_band := fun q hq => hd.2.2 q hq
    central_eq := ?_
    flatChart := C.flatChart.trans e.symm
    flat_source := ?_
    flat_smooth := hei.comp (C.flat_smooth.mono inter_subset_left) (fun _ hq => hq.2)
    flat_inverse := C.flat_inverse.comp (he.mono inter_subset_left) (fun _ hq => hq.2)
    flat_eq := ?_
    beta := C.beta * gamma
    beta_ne := mul_ne_zero C.beta_ne hgamma
    collarWidth := min 1 (C.collarWidth / (abs gamma + 1))
    collar_pos := lt_min zero_lt_one (div_pos C.collar_pos (by positivity))
    collar_le := min_le_left _ _
    collar_eq := ?_ }
  · intro q hq
    have hqt := (hd.2.2 q hq).2
    change psiNew (e.symm (C.sourceChart q), 0) = _
    rw [heq _ (e.map_target hqt) 0 (by norm_num), mul_zero, e.right_inv hqt]
    exact C.central_eq q (lt_of_lt_of_le hq hd.2.1)
  · intro x hx
    exact And.intro (C.flat_source hx)
      (hcap (C.flatChart_mem_sourceCap x (mem_closedBall_zero_iff.mp hx)))
  · intro q hq hx
    change e.symm (C.flatChart (heightCoordinates (q : E3)).1) = e.symm (C.sourceChart q)
    rw [C.flat_eq q hq hx]
  · intro x hx s hs
    have hxt := hcap (C.flatChart_mem_sourceCap x (by linarith))
    have hs1 : abs s < 1 := lt_of_lt_of_le hs (min_le_left _ _)
    have hden : 0 < abs gamma + 1 := by positivity
    have hsratio : abs s < C.collarWidth / (abs gamma + 1) :=
      lt_of_lt_of_le hs (min_le_right _ _)
    have htime : abs (gamma * s) < C.collarWidth := by
      calc
        abs (gamma * s) = abs gamma * abs s := abs_mul _ _
        _ <= (abs gamma + 1) * abs s :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg s)
        _ < C.collarWidth := by
          simpa only [mul_comm] using (lt_div_iff₀ hden).mp hsratio
    change psiNew (e.symm (C.flatChart x), s) = _
    rw [heq _ (e.map_target hxt) s hs1, e.right_inv hxt, C.collar_eq x hx (gamma * s) htime]
    simp only [mul_assoc]

theorem pullback_cap (C : SurgeryCapTag psi u)
    (e : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere)
    (he : ContMDiffOn I2 I2 CINF e e.source)
    (hei : ContMDiffOn I2 I2 CINF e.symm e.target)
    (gamma : Real) (hgamma : Ne gamma 0)
    (hcap : Set.Subset C.sourceCap e.target)
    (heq : forall p : UnitTwoSphere, e.source p -> forall s : Real, abs s < 1 ->
      psiNew (p, s) = psi (e p, gamma * s)) :
    (C.pullback e he hei gamma hgamma hcap heq).cap = C.cap := by
  rw [cap_eq_image, cap_eq_image]
  rfl

theorem pullback_seam (C : SurgeryCapTag psi u)
    (e : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere)
    (he : ContMDiffOn I2 I2 CINF e e.source)
    (hei : ContMDiffOn I2 I2 CINF e.symm e.target)
    (gamma : Real) (hgamma : Ne gamma 0)
    (hcap : Set.Subset C.sourceCap e.target)
    (heq : forall p : UnitTwoSphere, e.source p -> forall s : Real, abs s < 1 ->
      psiNew (p, s) = psi (e p, gamma * s)) :
    (C.pullback e he hei gamma hgamma hcap heq).seam = C.seam := by
  rw [seam_eq_image, seam_eq_image]
  rfl

end PoincareConjecture.M25.Topology3D.SurgeryCapTag
