import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Sweep.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.Transport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Compression.Slab
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere.Caps
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Restriction












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Compression

open Rounding

private abbrev E2 := EuclideanSpace Real (Fin 2)

variable {v : E2}

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)



def capSweepAffine (hv : ‖v‖ = 1) :
    Diffeomorph 𝓘(Real, Hemisphere.Plane v × Real) (𝓡 2)
      (Hemisphere.Plane v × Real) E2 ∞ := by
  let a := Real.sqrt 2
  have ha : a ≠ 0 := sqrt_two_pos.ne'
  let D : Diffeomorph 𝓘(Real, Hemisphere.Plane v × Real)
      𝓘(Real, Real × Hemisphere.Plane v)
      (Hemisphere.Plane v × Real) (Real × Hemisphere.Plane v) ∞ := {
    toFun := fun p => ((p.2 + 1) / a, a⁻¹ • p.1)
    invFun := fun p => (a • p.2, a * p.1 - 1)
    left_inv := by
      intro p
      apply Prod.ext
      · simp only [smul_smul, mul_inv_cancel₀ ha, one_smul]
      · change a * ((p.2 + 1) / a) - 1 = p.2
        field_simp
        <;> ring
    right_inv := by
      intro p
      apply Prod.ext
      · change (a * p.1 - 1 + 1) / a = p.1
        field_simp
        <;> ring
      · simp only [smul_smul, inv_mul_cancel₀ ha, one_smul]
    contMDiff_toFun := by
      change ContMDiff 𝓘(Real, Hemisphere.Plane v × Real)
        𝓘(Real, Real × Hemisphere.Plane v) ∞
        (fun p : Hemisphere.Plane v × Real => ((p.2 + 1) / a, a⁻¹ • p.1))
      apply ContDiff.contMDiff
      fun_prop
    contMDiff_invFun := by
      change ContMDiff 𝓘(Real, Real × Hemisphere.Plane v)
        𝓘(Real, Hemisphere.Plane v × Real) ∞
        (fun p : Real × Hemisphere.Plane v => (a • p.2, a * p.1 - 1))
      apply ContDiff.contMDiff
      fun_prop }
  exact D.trans (Poincare.Geometry.Euclidean.heightCoordinates hv).toDiffeomorph

@[simp] theorem capSweepAffine_apply (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    capSweepAffine hv p =
      ((p.2 + 1) / Real.sqrt 2) • v + (Real.sqrt 2)⁻¹ • (p.1 : E2) := rfl

theorem capSweepAffine_height (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    ⟪v, capSweepAffine hv p⟫ = (p.2 + 1) / Real.sqrt 2 := by
  exact Poincare.Geometry.Euclidean.inner_heightCoordinates hv _

theorem capSweepAffine_norm_sq (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    ‖capSweepAffine hv p‖ ^ 2 = (‖p.1‖ ^ 2 + (p.2 + 1) ^ 2) / 2 := by
  have hp := Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.1.property
  have hs := Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)
  rw [capSweepAffine_apply, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv, one_pow, mul_one,
    inner_smul_left, inner_smul_right, hp, mul_zero, add_zero, Submodule.norm_coe]
  field_simp [sqrt_two_pos.ne']
  nlinarith

theorem capSweepAffine_mem_closedBall (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    capSweepAffine hv p ∈ closedBall (0 : E2) 1 ↔
      ‖p.1‖ ^ 2 + (p.2 + 1) ^ 2 ≤ 2 := by
  rw [mem_closedBall, dist_zero_right]
  have h := capSweepAffine_norm_sq hv p
  constructor <;> intro hp <;> nlinarith [norm_nonneg (capSweepAffine hv p)]

theorem capSweepAffine_mem_ball (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    capSweepAffine hv p ∈ ball (0 : E2) 1 ↔
      ‖p.1‖ ^ 2 + (p.2 + 1) ^ 2 < 2 := by
  rw [mem_ball, dist_zero_right]
  have h := capSweepAffine_norm_sq hv p
  constructor <;> intro hp <;> nlinarith [norm_nonneg (capSweepAffine hv p)]

theorem capSweepAffine_mem_sphere (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    capSweepAffine hv p ∈ sphere (0 : E2) 1 ↔
      ‖p.1‖ ^ 2 + (p.2 + 1) ^ 2 = 2 := by
  rw [mem_sphere, dist_zero_right]
  have h := capSweepAffine_norm_sq hv p
  constructor <;> intro hp <;> nlinarith [norm_nonneg (capSweepAffine hv p)]


def unitBallSweepRange (hv : ‖v‖ = 1) : TopologicalSpace.Opens E2 :=
  ⟨(capSweepAffine hv).symm ⁻¹' sweepTarget,
    isOpen_sweepTarget.preimage (capSweepAffine hv).symm.continuous⟩


def unitBallSweepParametrization (hv : ‖v‖ = 1) :
    Diffeomorph 𝓘(Real, Hemisphere.Plane v × Real) (𝓡 2)
      (Hemisphere.Plane v × Real) (unitBallSweepRange hv) ∞ :=
  (capSweepParametrization 1).trans
    ((capSweepAffine hv).restrictOpens sweepRange (unitBallSweepRange hv)
      (fun p => by
        change (capSweepAffine hv).symm (capSweepAffine hv p) ∈ sweepTarget ↔ _
        rw [Diffeomorph.symm_apply_apply]
        rfl))


def unitBallSweepChart (hv : ‖v‖ = 1) :
    Diffeomorph (𝓡 2) 𝓘(Real, Hemisphere.Plane v × Real)
      (unitBallSweepRange hv) (Hemisphere.Plane v × Real) ∞ :=
  (unitBallSweepParametrization hv).symm

@[simp] theorem unitBallSweepParametrization_apply (hv : ‖v‖ = 1)
    (p : Hemisphere.Plane v × Real) :
    (unitBallSweepParametrization hv p : E2) =
      capSweepAffine hv (capSweepParametrization 1 p) := rfl

theorem unitBallSweepParametrization_mem_closedBall (hv : ‖v‖ = 1)
    (p : Hemisphere.Plane v × Real) :
    (unitBallSweepParametrization hv p : E2) ∈ closedBall 0 1 ↔ p.2 ∈ Icc (0 : Real) 1 := by
  rw [unitBallSweepParametrization_apply, capSweepAffine_mem_closedBall]
  simpa only [one_pow, one_add_one_eq_two] using capSweepParametrization_mem_quadratic_iff 1 p

theorem unitBallSweepParametrization_mem_ball (hv : ‖v‖ = 1)
    (p : Hemisphere.Plane v × Real) :
    (unitBallSweepParametrization hv p : E2) ∈ ball 0 1 ↔ p.2 ∈ Ioo (0 : Real) 1 := by
  rw [unitBallSweepParametrization_apply, capSweepAffine_mem_ball]
  simpa only [one_pow, one_add_one_eq_two] using
    capSweepParametrization_mem_quadratic_interior_iff 1 p

theorem unitBallSweepChart_closedBall (hv : ‖v‖ = 1) :
    closedBall (0 : E2) 1 ∩ unitBallSweepRange hv =
      (fun p : Hemisphere.Plane v × Real => (unitBallSweepParametrization hv p : E2)) ''
        {p | p.2 ∈ Icc (0 : Real) 1} := by
  ext y
  constructor
  · rintro ⟨hy, hyC⟩
    let z : unitBallSweepRange hv := ⟨y, hyC⟩
    refine ⟨unitBallSweepChart hv z, ?_, ?_⟩
    · apply (unitBallSweepParametrization_mem_closedBall hv _).mp
      simpa only [unitBallSweepChart, Diffeomorph.apply_symm_apply] using hy
    · exact congrArg Subtype.val ((unitBallSweepParametrization hv).apply_symm_apply z)
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(unitBallSweepParametrization_mem_closedBall hv p).mpr hp,
      (unitBallSweepParametrization hv p).property⟩

theorem unitBallSweepChart_ball (hv : ‖v‖ = 1) :
    ball (0 : E2) 1 ∩ unitBallSweepRange hv =
      (fun p : Hemisphere.Plane v × Real => (unitBallSweepParametrization hv p : E2)) ''
        {p | p.2 ∈ Ioo (0 : Real) 1} := by
  ext y
  constructor
  · rintro ⟨hy, hyC⟩
    let z : unitBallSweepRange hv := ⟨y, hyC⟩
    refine ⟨unitBallSweepChart hv z, ?_, ?_⟩
    · apply (unitBallSweepParametrization_mem_ball hv _).mp
      simpa only [unitBallSweepChart, Diffeomorph.apply_symm_apply] using hy
    · exact congrArg Subtype.val ((unitBallSweepParametrization hv).apply_symm_apply z)
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(unitBallSweepParametrization_mem_ball hv p).mpr hp,
      (unitBallSweepParametrization hv p).property⟩

private theorem image_open_cap (hv : ‖v‖ = 1) :
    (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' ball 0 1 =
      {y | y ∈ sphere (0 : E2) 1 ∧ (Real.sqrt 2)⁻¹ < ⟪v, y⟫} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Hemisphere.toSphere hv x).property, ?_⟩
    have := (Hemisphere.capHeight_lt_inner_toSphere_iff hv
      (show (0 : Real) ≤ 1 by norm_num) x).mpr (mem_ball_zero_iff.mp hx)
    simpa [Hemisphere.capHeight, one_add_one_eq_two] using this
  · rintro ⟨hy, hh⟩
    let p : sphere (0 : E2) 1 := ⟨y, hy⟩
    have hp : p ∈ Hemisphere.toSphere hv '' ball (0 : Hemisphere.Plane v) 1 := by
      rw [Hemisphere.image_ball_toSphere hv (show (0 : Real) ≤ 1 by norm_num)]
      simpa [Hemisphere.capHeight, p, one_add_one_eq_two] using hh
    obtain ⟨x, hx, heq⟩ := hp
    exact ⟨x, hx, congrArg Subtype.val heq⟩

private theorem image_closed_cap (hv : ‖v‖ = 1) :
    (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' closedBall 0 1 =
      {y | y ∈ sphere (0 : E2) 1 ∧ (Real.sqrt 2)⁻¹ ≤ ⟪v, y⟫} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Hemisphere.toSphere hv x).property, ?_⟩
    have := (Hemisphere.capHeight_le_inner_toSphere_iff hv
      (show (0 : Real) ≤ 1 by norm_num) x).mpr (by simpa using hx)
    simpa [Hemisphere.capHeight, one_add_one_eq_two] using this
  · rintro ⟨hy, hh⟩
    let p : sphere (0 : E2) 1 := ⟨y, hy⟩
    have hp : p ∈ Hemisphere.toSphere hv '' closedBall (0 : Hemisphere.Plane v) 1 := by
      rw [Hemisphere.image_closedBall_toSphere hv (show (0 : Real) ≤ 1 by norm_num)]
      simpa [Hemisphere.capHeight, p, one_add_one_eq_two] using hh
    obtain ⟨x, hx, heq⟩ := hp
    exact ⟨x, hx, congrArg Subtype.val heq⟩

private theorem image_cap_edge (hv : ‖v‖ = 1) :
    (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' sphere 0 1 =
      {y | y ∈ sphere (0 : E2) 1 ∧ ⟪v, y⟫ = (Real.sqrt 2)⁻¹} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Hemisphere.toSphere hv x).property, ?_⟩
    have hxnorm : ‖x‖ = 1 := by simpa using hx
    have hn := Hemisphere.norm_add_center_sq hv x
    rw [hxnorm] at hn
    have heq : ‖(x : E2) + v‖ = Real.sqrt 2 := by
      nlinarith [norm_nonneg ((x : E2) + v), sqrt_two_pos,
        Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)]
    rw [Hemisphere.inner_toSphere, heq]
  · rintro ⟨hy, hh⟩
    have hyclosed : y ∈ (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) ''
        closedBall 0 1 := by rw [image_closed_cap hv]; exact ⟨hy, hh.ge⟩
    obtain ⟨x, hx, rfl⟩ := hyclosed
    refine ⟨x, ?_, rfl⟩
    have hle : ‖x‖ ≤ 1 := by simpa using hx
    have hnot : ¬ ‖x‖ < 1 := by
      intro hlt
      have hi := (Hemisphere.capHeight_lt_inner_toSphere_iff hv
        (show (0 : Real) ≤ 1 by norm_num) x).mpr hlt
      have hi' : (Real.sqrt 2)⁻¹ < ⟪v, (Hemisphere.toSphere hv x : E2)⟫ := by
        simpa [Hemisphere.capHeight, one_add_one_eq_two] using hi
      linarith
    simpa using le_antisymm hle (le_of_not_gt hnot)

private theorem capSweepAffine_open_cap (hv : ‖v‖ = 1) (p : Hemisphere.Plane v × Real) :
    capSweepAffine hv p ∈
        (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' ball 0 1 ↔
      ‖p.1‖ ^ 2 + (p.2 + 1) ^ 2 = 2 ∧ 0 < p.2 := by
  rw [image_open_cap hv]
  change (capSweepAffine hv p ∈ sphere (0 : E2) 1 ∧
    (Real.sqrt 2)⁻¹ < ⟪v, capSweepAffine hv p⟫) ↔ _
  rw [capSweepAffine_mem_sphere, capSweepAffine_height]
  have hh : (Real.sqrt 2)⁻¹ < (p.2 + 1) / Real.sqrt 2 ↔ 0 < p.2 := by
    rw [inv_eq_one_div, div_lt_div_iff_of_pos_right sqrt_two_pos]
    constructor <;> intro h <;> linarith
  rw [hh]

theorem unitBallSweepChart_openDisk (hv : ‖v‖ = 1) :
    (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' ball 0 1 =
      (fun p : Hemisphere.Plane v × Real => (unitBallSweepParametrization hv p : E2)) ''
        {p | p.2 = 0} := by
  have hs := capSweepParametrization_image_boundary_zero (E := Hemisphere.Plane v) 1
  ext y
  constructor
  · intro hy
    let p := (capSweepAffine hv).symm y
    have hp : ‖p.1‖ ^ 2 + (p.2 + 1) ^ 2 = 2 ∧ 0 < p.2 := by
      apply (capSweepAffine_open_cap hv p).mp
      simpa [p] using hy
    have hpmem : p ∈ (fun x : Hemisphere.Plane v =>
        (capSweepParametrization 1 (x, 0) : Hemisphere.Plane v × Real)) '' univ := by
      rw [hs]
      simpa only [one_pow, one_add_one_eq_two, mem_ofPred_eq] using hp
    obtain ⟨x, _, hx⟩ := hpmem
    change (capSweepParametrization 1 (x, 0) : Hemisphere.Plane v × Real) = p at hx
    refine ⟨(x, 0), rfl, ?_⟩
    change (unitBallSweepParametrization hv (x, 0) : E2) = y
    rw [unitBallSweepParametrization_apply, hx]
    exact (capSweepAffine hv).apply_symm_apply y
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    change t = 0 at ht
    subst t
    change (unitBallSweepParametrization hv (x, 0) : E2) ∈ _
    rw [unitBallSweepParametrization_apply, capSweepAffine_open_cap]
    have h := hs.subset ⟨x, mem_univ _, rfl⟩
    simpa only [one_pow, one_add_one_eq_two, mem_ofPred_eq] using h

private theorem unitBallSweepRange_sphere_iff (hv : ‖v‖ = 1) {y : E2}
    (hy : y ∈ sphere (0 : E2) 1) :
    y ∈ unitBallSweepRange hv ↔ ⟪v, y⟫ ≠ (Real.sqrt 2)⁻¹ := by
  let p := (capSweepAffine hv).symm y
  have he : capSweepAffine hv p = y := (capSweepAffine hv).apply_symm_apply y
  have hn := (capSweepAffine_mem_sphere hv p).mp (he ▸ hy)
  have hh : ⟪v, y⟫ = (p.2 + 1) / Real.sqrt 2 := by rw [← he, capSweepAffine_height]
  have hz : p.2 = 0 ↔ ⟪v, y⟫ = (Real.sqrt 2)⁻¹ := by
    rw [hh, inv_eq_one_div, div_left_inj' sqrt_two_pos.ne']
    constructor <;> intro h <;> linarith
  change (p.2 ≠ 0 ∨ ‖p.1‖ < 1) ↔ _
  constructor
  · rintro (hp | hp)
    · exact fun h => hp (hz.mpr h)
    · intro hh
      have hw := hz.mpr hh
      rw [hw] at hn
      nlinarith [norm_nonneg p.1]
  · intro hh
    exact Or.inl (fun h => hh (hz.mp h))

theorem unitBallSweepChart_closedDisk (hv : ‖v‖ = 1) :
    ((fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' closedBall 0 1) ∩
        unitBallSweepRange hv =
      (fun p : Hemisphere.Plane v × Real => (unitBallSweepParametrization hv p : E2)) ''
        {p | p.2 = 0} := by
  rw [← unitBallSweepChart_openDisk hv, image_closed_cap hv, image_open_cap hv]
  ext y
  constructor
  · rintro ⟨⟨hy, hle⟩, hC⟩
    have hne := (unitBallSweepRange_sphere_iff hv hy).mp hC
    exact ⟨hy, lt_of_le_of_ne hle (Ne.symm hne)⟩
  · rintro ⟨hy, hlt⟩
    exact ⟨⟨hy, hlt.le⟩, (unitBallSweepRange_sphere_iff hv hy).mpr hlt.ne'⟩

theorem unitBallSweepChart_edge (hv : ‖v‖ = 1) :
    closedBall (0 : E2) 1 \ unitBallSweepRange hv ⊆
      (fun x : Hemisphere.Plane v => (Hemisphere.toSphere hv x : E2)) '' sphere 0 1 := by
  intro y hy
  let p := (capSweepAffine hv).symm y
  have he : capSweepAffine hv p = y := (capSweepAffine hv).apply_symm_apply y
  have hn := (capSweepAffine_mem_closedBall hv p).mp (he ▸ hy.1)
  have hnot : ¬ (p.2 ≠ 0 ∨ ‖p.1‖ < 1) := hy.2
  have hw : p.2 = 0 := not_ne_iff.mp (fun h => hnot (Or.inl h))
  have hr : 1 ≤ ‖p.1‖ := le_of_not_gt (fun h => hnot (Or.inr h))
  have hr' : ‖p.1‖ = 1 := by rw [hw] at hn; nlinarith [norm_nonneg p.1]
  rw [image_cap_edge hv]
  refine ⟨?_, ?_⟩
  · rw [← he, capSweepAffine_mem_sphere, hw, hr']
    norm_num
  · rw [← he, capSweepAffine_height, hw]
    simp [one_div]

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : E2) 1



theorem exists_marked_disk_sweep
    (b : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (g : E1 → S1) (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E1) 1,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x) :
    ∃ C : Opens E2,
      ∃ e : Diffeomorph (𝓡 2) 𝓘(Real, Hemisphere.Plane (g 0 : E2) × Real)
          C (Hemisphere.Plane (g 0 : E2) × Real) ∞,
        (b '' closedBall 0 1) ∩ C =
          (fun p => (e.symm p : E2)) '' {p | 0 ≤ p.2 ∧ p.2 ≤ 1} ∧
        (b '' ball 0 1) ∩ C =
          (fun p => (e.symm p : E2)) '' {p | 0 < p.2 ∧ p.2 < 1} ∧
        (fun x => b (g x)) '' ball (0 : E1) 1 =
          (fun p => (e.symm p : E2)) '' {p | p.2 = 0} ∧
        ((fun x => b (g x)) '' closedBall (0 : E1) 1) ∩ C =
          (fun p => (e.symm p : E2)) '' {p | p.2 = 0} ∧
        (b '' closedBall 0 1) \ C ⊆
          (fun x => b (g x)) '' sphere (0 : E1) 1 := by
  obtain ⟨J, H, hHB, hHBopen, _, _, hHD, hHDopen, hHE⟩ :=
    Normalization.exists_ambient_disk_normalization b g hgi hgl
  let hv := norm_eq_of_mem_sphere (g 0)
  let C₀ := unitBallSweepRange hv
  let e₀ := unitBallSweepChart hv
  let C := pullbackOpen H C₀
  let e := (pullbackDiffeomorph H C₀).trans e₀
  have hcoord (p : Hemisphere.Plane (g 0 : E2) × Real) :
      (e.symm p : E2) = H.symm (e₀.symm p : E2) := rfl
  have hclosed := pullback_image_inter H C₀ e₀.symm hHB
    (unitBallSweepChart_closedBall hv)
  have hopen := pullback_image_inter H C₀ e₀.symm hHBopen
    (unitBallSweepChart_ball hv)
  have hdisk := pullback_image_inter H C₀ e₀.symm hHD
    (unitBallSweepChart_closedDisk hv)
  refine ⟨C, e, hclosed, hopen, ?_, hdisk, ?_⟩
  · apply (H.toEquiv.injective.image_injective)
    change H '' ((fun x => b (g x)) '' ball (0 : E1) 1) =
      H '' ((fun p => (e.symm p : E2)) '' {p | p.2 = 0})
    rw [hHDopen, unitBallSweepChart_openDisk hv, image_image]
    apply image_congr
    intro p _
    change (unitBallSweepParametrization hv p : E2) = H (H.symm (e₀.symm p : E2))
    rw [H.apply_symm_apply]
    rfl
  · intro y hy
    have hHy : H y ∈ closedBall (0 : E2) 1 := hHB ▸ mem_image_of_mem H hy.1
    have hnot : H y ∉ C₀ := hy.2
    have hedge := unitBallSweepChart_edge hv ⟨hHy, hnot⟩
    rw [← hHE] at hedge
    obtain ⟨z, hz, he⟩ := hedge
    exact H.injective he ▸ hz





theorem exists_marked_disk_compression
    (b : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (g : E1 → S1) (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E1) 1,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x)
    (W O : Set E2) (hW : IsOpen W) (hO : IsOpen O)
    (hDW : (fun x => b (g x)) '' closedBall (0 : E1) 1 ⊆ W)
    (hBO : b '' closedBall (0 : E2) 1 ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => b (g x)) '' closedBall (0 : E1) 1) ∧
      ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∉ K, F x = x) ∧
        F '' (b '' closedBall (0 : E2) 1) ⊆
          (b '' closedBall (0 : E2) 1) ∩ W := by
  obtain ⟨C, e, hslab, _, _, hzero, hedge⟩ :=
    exists_marked_disk_sweep b g hgi hgl
  exact exists_slab_compression C e ((isCompact_closedBall 0 1).image b.continuous)
    hW hO hslab hzero (hedge.trans (image_mono sphere_subset_closedBall)) hDW hBO



end Poincare.Manifold.Schoenflies.PlaneArcs.Compression
