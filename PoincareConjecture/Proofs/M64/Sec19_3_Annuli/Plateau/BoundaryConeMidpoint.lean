import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeHalfDisk
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeH1Radius

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture.M64BoundaryCone

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

open M65Interior

def halfConeDiameter (r : ℝ) (a b : C) (s : ℝ) : C :=
  AffineMap.lineMap b a ((s + r) / (2 * r))

theorem midpoint_cone_diameter {r : ℝ} (hr : r ≠ 0)
    (v : ℝ → C) (s : ℝ) :
    let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
    coneCoordinates r m v s 0 = halfConeDiameter r (v 0) (v Real.pi) s ∧
      coneCoordinates r m v s Real.pi = halfConeDiameter r (v 0) (v Real.pi) (-s) := by
  have hratio (t : ℝ) : (t + r) / (2 * r) = 1 / 2 + (t / r) / 2 := by
    field_simp
    ring
  constructor <;>
    simp only [coneCoordinates, halfConeDiameter, AffineMap.lineMap_apply_module, hratio] <;>
    module

theorem midpoint_mem_closedBall {ρ : ℝ} {a b : C}
    (ha : a ∈ closedBall 0 ρ) (hb : b ∈ closedBall 0 ρ) :
    (1 / 2 : ℝ) • (a + b) ∈ closedBall 0 ρ := by
  have h := (convex_closedBall (0 : C) ρ) ha hb
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  simpa only [smul_add] using h

theorem midpoint_halfCone_green [CompleteSpace C] [ProperSpace C] {g : C → ℝ}
    {v d : ℝ → C} {r ρ K : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ θ in s..t, d θ)
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
    IntegrableOn (fun z => coneDiskField g r m v d 0 i z * test z +
      coneDiskMap g r m v 0 z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      coneDiskField g r m v d 0 i z * test z + coneDiskMap g r m v 0 z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        g (v θ) * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
        ∫ s in (-r)..r, g (halfConeDiameter r (v 0) (v Real.pi) s) *
          test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let L := halfConeDiameter r (v 0) (v Real.pi)
  let h := fun s => g (L s) * test (s • e 0)
  have h0 : m ∈ closedBall 0 ρ := midpoint_mem_closedBall
    (hvb (by exact ⟨le_rfl, Real.pi_pos.le⟩)) (hvb (by exact ⟨Real.pi_pos.le, le_rfl⟩))
  have hLc : Continuous L := by
    change Continuous (fun s => halfConeDiameter r (v 0) (v Real.pi) s)
    simp only [halfConeDiameter, AffineMap.lineMap_apply_module]
    fun_prop
  have hLm : MapsTo L (Icc (-r) r) (ball 0 (2 * ρ)) := by
    intro s hs
    apply (closedBall_subset_ball (by linarith : ρ < 2 * ρ))
    apply (convex_closedBall (0 : C) ρ).mapsTo_lineMap
      (hvb (by exact ⟨Real.pi_pos.le, le_rfl⟩)) (hvb (by exact ⟨le_rfl, Real.pi_pos.le⟩))
    exact ⟨div_nonneg (by linarith [hs.1]) (by linarith),
      (div_le_one (by linarith : 0 < 2 * r)).mpr (by linarith [hs.2])⟩
  have hc : ContinuousOn h (Icc (-r) r) :=
    (hg.continuousOn.comp hLc.continuousOn hLm).mul
      (ht.continuous.comp (continuous_id.smul continuous_const)).continuousOn
  have hi : IntervalIntegrable h volume (-r) r := hc.intervalIntegrable_of_Icc (by linarith)
  have hi0 : IntervalIntegrable h volume 0 r := hi.mono_set (by
    rw [uIcc_of_le hr.le, uIcc_of_le (by linarith : -r ≤ r)]
    exact Icc_subset_Icc (by linarith) le_rfl)
  have hi1 : IntervalIntegrable h volume (-r) 0 := hi.mono_set (by
    rw [uIcc_of_le (by linarith : -r ≤ 0), uIcc_of_le (by linarith : -r ≤ r)]
    exact Icc_subset_Icc le_rfl hr.le)
  have hneg : IntervalIntegrable (fun s => h (-s)) volume 0 r := by
    have hcneg : ContinuousOn (fun s => h (-s)) (Icc (0 : ℝ) r) :=
      hc.comp continuous_neg.continuousOn (by
        intro s hs
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    exact hcneg.intervalIntegrable_of_Icc hr.le
  have hpi : Proofs.M58.angularPoint Real.pi = -(e 0) := by
    ext j
    fin_cases j <;> simp [e, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  have hz : Proofs.M58.angularPoint 0 = e 0 := by
    ext j
    fin_cases j <;> simp [e, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  have htpi : Proofs.M58.angularVector Real.pi = -(e 1) := by
    ext j
    fin_cases j <;> simp [e, Proofs.M58.angularVector, EuclideanSpace.basisFun_apply]
  have htz : Proofs.M58.angularVector 0 = e 1 := by
    ext j
    fin_cases j <;> simp [e, Proofs.M58.angularVector, EuclideanSpace.basisFun_apply]
  have hedge : (∫ s in (0 : ℝ)..r,
      coneAngularFlux g r m v 0 test i s Real.pi - coneAngularFlux g r m v 0 test i s 0) =
        -(e 1 i * ∫ s in (-r)..r, h s) := by
    have heq (s : ℝ) : coneAngularFlux g r m v 0 test i s Real.pi -
        coneAngularFlux g r m v 0 test i s 0 = -(e 1 i * (h (-s) + h s)) := by
      dsimp only [coneAngularFlux, polarPlane]
      rw [(midpoint_cone_diameter hr.ne' v s).1, (midpoint_cone_diameter hr.ne' v s).2]
      simp only [hpi, hz, htpi, htz, zero_add, PiLp.neg_apply, smul_neg, ← neg_smul]
      dsimp only [h, L]
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hneg hi0, intervalIntegral.integral_comp_neg, neg_zero,
      intervalIntegral.integral_add_adjacent_intervals hi1 hi0]
  have hgreen := halfCone_green hr hρ hK hv hg h0 hvb hd hinc hD 0 test ht i
  rw [hedge] at hgreen
  refine ⟨hgreen.1, ?_⟩
  simpa [polarPlane, m, e, h, L, sub_eq_add_neg] using hgreen.2

theorem midpoint_angular_energy_le {v d : ℝ → C}
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ θ in s..t, d θ) :
    (∫ θ in Icc (0 : ℝ) Real.pi,
      (‖v θ - (1 / 2 : ℝ) • (v 0 + v Real.pi)‖ ^ 2 + ‖d θ‖ ^ 2)) ≤
      (1 + 4 * Real.pi ^ 2) * ∫ θ in Icc (0 : ℝ) Real.pi, ‖d θ‖ ^ 2 := by
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  let E := ∫ θ in Icc (0 : ℝ) Real.pi, ‖d θ‖ ^ 2
  have hFTC := fun t ht => hinc 0 ⟨le_rfl, Real.pi_pos.le⟩ t ht
  have h0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) :=
    m64H1Trace_oscillation_sq_le v d hd hFTC ht ⟨le_rfl, Real.pi_pos.le⟩
  have hπ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) :=
    m64H1Trace_oscillation_sq_le v d hd hFTC ht ⟨Real.pi_pos.le, le_rfl⟩
  have hp (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) : ‖v θ - m‖ ^ 2 ≤ 4 * Real.pi * E := by
    let A := v θ - v 0
    let B := v θ - v Real.pi
    have he : v θ - m = (1 / 2 : ℝ) • (A + B) := by
      dsimp only [m, A, B]
      module
    have hn := pow_le_pow_left₀ (norm_nonneg (A + B)) (norm_add_le A B) 2
    have hA := h0 θ hθ
    have hB := hπ θ hθ
    rw [he, norm_smul]
    norm_num
    change ‖A‖ ^ 2 ≤ 4 * Real.pi * E at hA
    change ‖B‖ ^ 2 ≤ 4 * Real.pi * E at hB
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  have hm : IntegrableOn (fun θ => ‖v θ - m‖ ^ 2) (Icc (0 : ℝ) Real.pi) :=
    ((hv.sub continuousOn_const).norm.pow 2).integrableOn_compact isCompact_Icc
  have hle := integral_mono_ae hm (integrable_const (4 * Real.pi * E))
    (ae_restrict_of_forall_mem measurableSet_Icc hp)
  have hle' : (∫ θ in Icc (0 : ℝ) Real.pi, ‖v θ - m‖ ^ 2) ≤ 4 * Real.pi ^ 2 * E := by
    simp only [integral_const, Measure.restrict_apply_univ, Measure.real,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul] at hle
    nlinarith only [hle]
  rw [integral_add hm hd.norm.integrable_sq]
  dsimp only [E] at hle'
  nlinarith only [hle']

theorem midpoint_halfCone_derivativeEnergy_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : C → E} {v d : ℝ → C} {r ρ K : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ θ in s..t, d θ)
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K) :
    let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
    IntegrableOn (fun z => ∑ i : Fin 2, ‖coneDiskField g r m v d 0 i z‖ ^ 2)
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      ∑ i : Fin 2, ‖coneDiskField g r m v d 0 i z‖ ^ 2) ≤
      (K ^ 2 / 2) * (1 + 4 * Real.pi ^ 2) *
        ∫ θ in Icc (0 : ℝ) Real.pi, ‖d θ‖ ^ 2 := by
  have h0 := midpoint_mem_closedBall
    (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
  obtain ⟨hI, hE⟩ := halfCone_derivativeEnergy_le hr hρ hK hv hg h0 hvb hd hD 0
  refine ⟨hI, hE.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (midpoint_angular_energy_le hv hd hinc) (div_nonneg (sq_nonneg K) (by norm_num))

end PoincareConjecture.M64BoundaryCone
