import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakGraph
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityACComposition
import Mathlib.MeasureTheory.Measure.OpenPos











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap ENNReal

namespace PoincareConjecture.M65Boundary

open M65Interior



def boundaryCirclePoint {p : ℂ} (hp : ‖p‖ = 1) (s : ℝ) : LoopCircle :=
  ⟨diskBoundaryCoordinate p (s • EuclideanSpace.basisFun (Fin 2) ℝ 0), by
    rw [norm_diskBoundaryCoordinate hp]
    simp [EuclideanSpace.basisFun_apply]⟩




theorem halfDisk_ae_semicircle {H ε R : ℝ} (hε : 0 < ε) (hRH : R ≤ H)
    {Q : LoopPlane → Prop}
    (hQ : ∀ᵐ z ∂volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}), Q z) :
    ∀ᵐ r ∂volume.restrict (Icc ε R), ∀ᵐ θ ∂volume.restrict (Icc (0 : ℝ) Real.pi),
      Q (r • Proofs.M58.angularPoint θ) := by
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  have hK : MeasurableSet K := isClosed_closedBall.measurableSet.inter
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hglobal : ∀ᵐ z ∂(volume : Measure LoopPlane), z ∈ K → Q z :=
    (ae_restrict_iff' hK).mp hQ
  have hangle : Icc (0 : ℝ) Real.pi ⊆ Icc (-Real.pi) Real.pi :=
    Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hm := (polarPlane_measurePreserving (0 : LoopPlane)).measurable
  have hdom : Measure.map (polarPlane 0)
      ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))) ≤
      (ENNReal.ofReal ε)⁻¹ • (volume : Measure LoopPlane) :=
    (Measure.map_mono (Measure.prod_mono le_rfl
    (Measure.restrict_mono hangle le_rfl)) hm).trans (polarPlane_map_strip_le 0 hε)
  have hp := Measure.ae_ae_of_ae_prod (ae_of_ae_map hm.aemeasurable
    (ae_mono hdom (Measure.ae_smul_measure hglobal (ENNReal.ofReal ε)⁻¹)))
  filter_upwards [hp, ae_restrict_mem measurableSet_Icc] with r hr hrI
  filter_upwards [hr, ae_restrict_mem measurableSet_Icc] with θ hθ hθI
  simp only [polarPlane, zero_add] at hθ
  apply hθ
  constructor
  · rw [mem_closedBall_zero_iff]
    simpa only [polarPlane, zero_add, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hε.le.trans hrI.1), Proofs.M58.norm_angularPoint, mul_one]
      using hrI.2.trans hRH
  · change 0 ≤ (r • Proofs.M58.angularPoint θ) 1
    simp only [PiLp.smul_apply, smul_eq_mul, Proofs.M58.angularPoint,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact mul_nonneg (hε.le.trans hrI.1) (Real.sin_nonneg_of_mem_Icc hθI)

private theorem scalar_original_semicircle_uniform :
    ∃ R : ℝ, 0 < R ∧ ∀ {p : ℂ} (hp : ‖p‖ = 1)
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (_htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b))
    {u0 : LoopPlane → ℝ} {d0 : Fin 2 → LoopPlane → ℝ}
    (_hu0 : u =ᵐ[volume.restrict loopDiskSet] u0)
    (_hd0 : ∀ i, d i =ᵐ[volume.restrict loopDiskSet] d0 i)
    (b0 : C(LoopCircle, ℝ))
    (_hb0 : m65CircleBoundaryPullback b =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => b0 ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩),
      let P := diskBoundaryCoordinate p
      let D := fun i z => ∑ j : Fin 2,
        (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d0 j (P z)
      ∀ ε : ℝ, 0 < ε → ∀ᵐ r ∂volume.restrict (Icc ε R),
        MemLp (fun θ => -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
          r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ))
            2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
        ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 Real.pi ∧
          (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
            fun θ => u0 (P (r • Proofs.M58.angularPoint θ))) ∧
          v 0 = b0 (boundaryCirclePoint hp r) ∧
          v Real.pi = b0 (boundaryCirclePoint hp (-r)) ∧
          (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
            v t - v s = ∫ θ in s..t,
              -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
                r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ)) ∧
          ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
            (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
              D i z * test z + u0 (P z) *
                fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
              r * (∫ θ in (0 : ℝ)..Real.pi,
                v θ * test (r • Proofs.M58.angularPoint θ) *
                  Proofs.M58.angularPoint θ i) -
                (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                  ∫ s in (-r)..r, b0 (boundaryCirclePoint hp s) *
                    test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  obtain ⟨R0, hR0, hgraph⟩ := weakTrace_boundary_halfDisk_uniform
  obtain ⟨R1, hR1, hgeometry⟩ := exists_uniform_boundary_halfDisk_pullback
  let R := min R0 (min R1 Real.pi)
  have hR : 0 < R := lt_min hR0 (lt_min hR1 Real.pi_pos)
  refine ⟨R, hR, ?_⟩
  intro p hp u d b htrace u0 d0 hu0 hd0 b0 hb0
  obtain ⟨U, D, B, hU, hD, hB, hG⟩ := hgraph p hp u d b htrace
  obtain ⟨_hleft, _hcap, _hinv, C, _hC, hmap⟩ := hgeometry p hp
  have hRR0 : R ≤ R0 := min_le_left _ _
  have hRR1 : R ≤ R1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRπ : R ≤ Real.pi := (min_le_right _ _).trans (min_le_right _ _)
  let P := diskBoundaryCoordinate p
  let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  let D0 := fun i z => ∑ j : Fin 2,
    (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d0 j (P z)
  have hP : Continuous P := (contDiff_diskBoundaryCoordinate p).continuous
  have hKK0 : K ⊆ closedBall (0 : LoopPlane) R0 ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter (closedBall_subset_closedBall hRR0) Subset.rfl
  have hKK1 : K ⊆ closedBall (0 : LoopPlane) R1 ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter (closedBall_subset_closedBall hRR1) Subset.rfl
  have hpull : ∀ {Q : LoopPlane → Prop}, (∀ᵐ z ∂volume.restrict loopDiskSet, Q z) →
      ∀ᵐ z ∂volume.restrict K, Q (P z) := by
    intro Q hQ
    exact ae_restrict_of_ae_restrict_of_subset hKK1 (ae_of_ae_map hP.measurable.aemeasurable
      (ae_mono hmap (Measure.ae_smul_measure hQ C)))
  have hU0 : U =ᵐ[volume.restrict K] fun z => u0 (P z) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKK0 hU, hpull hu0] with z hz hz'
    exact hz.trans hz'
  have hD0 (i : Fin 2) : D i =ᵐ[volume.restrict K] D0 i := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKK0 (hD i),
      ae_all_iff.mpr (fun j => hpull (hd0 j))] with z hz hd
    rw [hz]
    exact Finset.sum_congr rfl (fun j _ => congrArg (_ * ·) (hd j))
  have hcircle : IsClosed {z : LoopPlane | ‖z‖ = 1} :=
    isClosed_eq continuous_norm continuous_const
  obtain ⟨bext, hbext⟩ := b0.exists_extension' hcircle.isClosedEmbedding_subtypeVal
  have hbextAE : b =ᵐ[m65CircleBoundaryMeasure] bext := by
    have hm : MeasurableSet {z : LoopPlane | b z = bext z} :=
      (isClosed_eq (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
        continuous_snd).measurableSet.preimage
          ((Lp.stronglyMeasurable b).measurable.prodMk bext.continuous.measurable)
    apply (ae_map_iff Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable hm).mpr
    filter_upwards [(m65CircleBoundaryPullback_coe b).symm.trans hb0] with t ht
    exact ht.trans (congrFun hbext
      ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩).symm
  let Q := fun s : ℝ => P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hQ : Continuous Q := hP.comp (continuous_id.smul continuous_const)
  obtain ⟨C1, _hC1, hmap1⟩ := diameter_measure_bound hp hRπ
  have hB0 : B =ᵐ[volume.restrict (Icc (-R) R)]
      fun s => b0 (boundaryCirclePoint hp s) := by
    have hBR := ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc (neg_le_neg hRR0) hRR0) hB
    have hBa := ae_of_ae_map hQ.measurable.aemeasurable
      (ae_mono hmap1 (Measure.ae_smul_measure hbextAE C1))
    filter_upwards [hBR, hBa] with s hs hs'
    exact hs.trans (hs'.trans (congrFun hbext (boundaryCirclePoint hp s)))
  have hneg : ∀ᵐ s ∂volume.restrict (Icc (-R) R),
      B (-s) = b0 (boundaryCirclePoint hp (-s)) := by
    have hm := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage_emb
      (Homeomorph.neg ℝ).measurableEmbedding (Icc (-R) R)
    have heq : (fun s : ℝ => -s) ⁻¹' Icc (-R) R = Icc (-R) R := by
      ext s
      simp only [mem_preimage, mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith
    rw [heq] at hm
    exact hm.quasiMeasurePreserving.ae hB0
  dsimp only
  intro ε hε
  have hrad : Icc ε R ⊆ Icc (-R) R := Icc_subset_Icc
    (by linarith [hR]) le_rfl
  have hincAE := ae_all_iff.mpr fun i =>
    halfDisk_ae_semicircle hε (le_refl R) (hD0 i)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl hRR0) (hG ε hε),
    halfDisk_ae_semicircle hε (le_refl R) hU0, hincAE,
    ae_restrict_of_ae_restrict_of_subset hrad hB0,
    ae_restrict_of_ae_restrict_of_subset hrad hneg,
    ae_restrict_mem measurableSet_Icc] with r hr hu hd hb hn hrI
  obtain ⟨hmd, v, hv, hvU, hv0, hvπ, hvi, hgr⟩ := hr
  have hfield : (fun θ => -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
      r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ))
      =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
        fun θ => -r * Real.sin θ * D0 0 (r • Proofs.M58.angularPoint θ) +
          r * Real.cos θ * D0 1 (r • Proofs.M58.angularPoint θ) := by
    filter_upwards [hd 0, hd 1] with θ h0 h1
    rw [h0, h1]
  refine ⟨hmd.ae_eq hfield, v, hv, hvU.trans hu, hv0.trans hb, hvπ.trans hn, ?_, ?_⟩
  · intro s hs t ht
    rw [hvi s hs t ht]
    apply intervalIntegral.integral_congr_ae_restrict
    exact ae_restrict_of_ae_restrict_of_subset
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)) hfield
  · intro test i
    have hKr : closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} ⊆ K :=
      inter_subset_inter (closedBall_subset_closedBall hrI.2) Subset.rfl
    have hvol : (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        D0 i z * test z + u0 (P z) *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
          D i z * test z + U z *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hKr (hD0 i),
        ae_restrict_of_ae_restrict_of_subset hKr hU0] with z hz hz'
      rw [hz, hz']
    rw [hvol, hgr test i]
    congr 2
    apply intervalIntegral.integral_congr_ae_restrict
    have hrpos : 0 ≤ r := hε.le.trans hrI.1
    have hsub : uIoc (-r) r ⊆ Icc (-R) R := by
      rw [uIoc_of_le (by linarith)]
      exact Ioc_subset_Icc_self.trans (Icc_subset_Icc (neg_le_neg hrI.2) hrI.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hB0] with s hs
    rw [hs]



def weakDiskBoundaryField {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (p : ℂ) (i : Fin 2) (z : LoopPlane) :
    EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun l =>
  ∑ k : Fin 2, (fderiv ℝ (diskBoundaryCoordinate p) z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)) k * F.derivative k (diskBoundaryCoordinate p z) l

private theorem closedTarget_of_ae {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    (hS : IsClosed S) (hne : S.Nonempty) {v : ℝ → EuclideanSpace ℝ (Fin N)}
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hmem : ∀ᵐ θ ∂volume.restrict (Icc (0 : ℝ) Real.pi), v θ ∈ S) :
    MapsTo v (Icc (0 : ℝ) Real.pi) S := by
  have hz : (fun θ => infDist (v θ) S) =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
      fun _ => (0 : ℝ) := hmem.mono fun _ h => infDist_zero_of_mem h
  have heq := Measure.eqOn_of_ae_eq hz
    ((continuous_infDist_pt S).comp_continuousOn hv) continuousOn_const
    (closure_interior_Icc Real.pi_pos.ne).symm.subset
  exact fun θ hθ => (hS.mem_iff_infDist_zero hne).mpr (heq hθ)






theorem weakDisk_boundary_semicircle_uniform {M : Type*} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (he : Continuous e) (hγ : Continuous γ) (heclosed : IsClosed (range e)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1),
      ∀ ε : ℝ, 0 < ε → ∀ᵐ r ∂volume.restrict (Icc ε R),
      let P := diskBoundaryCoordinate p
      let D := weakDiskBoundaryField F p
      let d := fun θ => (-r * Real.sin θ) • D 0 (r • Proofs.M58.angularPoint θ) +
        (r * Real.cos θ) • D 1 (r • Proofs.M58.angularPoint θ)
      MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      ∃ v : ℝ → EuclideanSpace ℝ (Fin N),
        AbsolutelyContinuousOnInterval v 0 Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
          fun θ => e (F.value (P (r • Proofs.M58.angularPoint θ)))) ∧
        MapsTo v (Icc (0 : ℝ) Real.pi) (range e) ∧
        v 0 = e (γ (F.parameter (boundaryCirclePoint hp r))) ∧
        v Real.pi = e (γ (F.parameter (boundaryCirclePoint hp (-r)))) ∧
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ θ in s..t, d θ) ∧
        ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
            D i z j * test z + e (F.value (P z)) j *
              fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            r * (∫ θ in (0 : ℝ)..Real.pi,
              v θ j * test (r • Proofs.M58.angularPoint θ) *
                Proofs.M58.angularPoint θ i) -
              (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
                  test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  obtain ⟨R, hR, hscalar⟩ := scalar_original_semicircle_uniform
  refine ⟨R, hR, ?_⟩
  intro F p hp
  let b (j : Fin N) : C(LoopCircle, ℝ) :=
    ⟨fun q => e (γ (F.parameter q)) j,
      (EuclideanSpace.proj j).continuous.comp (he.comp (hγ.comp F.parameter.continuous))⟩
  have hu (j : Fin N) : m65DiskCoordinateL2 F.embeddedValue j
      =ᵐ[volume.restrict loopDiskSet] fun z => e (F.value z) j := by
    filter_upwards [m65DiskCoordinateL2_coe F.embeddedValue j, F.embeddedValue_ae] with z hz hz'
    exact hz.trans (congrArg (fun w : EuclideanSpace ℝ (Fin N) => w j) hz')
  have hG := fun j => hscalar hp (F.weak_trace j) (hu j)
    (fun i => m65DiskCoordinateL2_coe (F.derivative i) j) (b j) (F.boundary_ae j)
  intro ε hε
  have hGj (j : Fin N) := hG j ε hε
  filter_upwards [ae_all_iff.mpr hGj] with r hr
  choose v hv hve hv0 hvπ hvi hgr using fun j => (hr j).2
  let V (θ : ℝ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun j => v j θ
  let d (θ : ℝ) := (-r * Real.sin θ) • weakDiskBoundaryField F p 0 (r • Proofs.M58.angularPoint θ) +
    (r * Real.cos θ) • weakDiskBoundaryField F p 1 (r • Proofs.M58.angularPoint θ)
  have hm : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) :=
    MemLp.of_eval_piLp fun j => (hr j).1
  have hAC : AbsolutelyContinuousOnInterval V 0 Real.pi := coordinatewise_ac hv
  have hcont : ContinuousOn V (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hAC.continuousOn
  have hAE : V =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
      fun θ => e (F.value (diskBoundaryCoordinate p (r • Proofs.M58.angularPoint θ))) := by
    filter_upwards [ae_all_iff.mpr hve] with θ hθ
    ext j
    exact hθ j
  have hmaps : MapsTo V (Icc (0 : ℝ) Real.pi) (range e) :=
    closedTarget_of_ae heclosed ⟨e (F.value 0), mem_range_self _⟩ hcont
      (hAE.mono fun θ hθ => hθ ▸ mem_range_self _)
  refine ⟨hm, V, hAC, hAE, hmaps, ?_, ?_, ?_, ?_⟩
  · ext j
    exact hv0 j
  · ext j
    exact hvπ j
  · intro s hs t ht
    have hdi : IntegrableOn d (Icc (0 : ℝ) Real.pi) :=
      hm.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hi : IntervalIntegrable d volume s t :=
      (hdi.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
    ext j
    change v j t - v j s = (EuclideanSpace.proj j) (∫ θ in s..t, d θ)
    rw [← (EuclideanSpace.proj j).intervalIntegral_comp_comm hi]
    exact hvi j s hs t ht
  · intro test i j
    exact hgr j test i



theorem weakDisk_boundary_semicircle {M : Type*} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (he : Continuous e) (hγ : Continuous γ)
    (heclosed : IsClosed (range e)) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε → ∀ᵐ r ∂volume.restrict (Icc ε R),
      let P := diskBoundaryCoordinate p
      let D := weakDiskBoundaryField F p
      let d := fun θ => (-r * Real.sin θ) • D 0 (r • Proofs.M58.angularPoint θ) +
        (r * Real.cos θ) • D 1 (r • Proofs.M58.angularPoint θ)
      MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      ∃ v : ℝ → EuclideanSpace ℝ (Fin N),
        AbsolutelyContinuousOnInterval v 0 Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
          fun θ => e (F.value (P (r • Proofs.M58.angularPoint θ)))) ∧
        MapsTo v (Icc (0 : ℝ) Real.pi) (range e) ∧
        v 0 = e (γ (F.parameter (boundaryCirclePoint hp r))) ∧
        v Real.pi = e (γ (F.parameter (boundaryCirclePoint hp (-r)))) ∧
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ θ in s..t, d θ) ∧
        ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
            D i z j * test z + e (F.value (P z)) j *
              fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            r * (∫ θ in (0 : ℝ)..Real.pi,
              v θ j * test (r • Proofs.M58.angularPoint θ) *
                Proofs.M58.angularPoint θ i) -
              (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
                  test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  obtain ⟨R, hR, h⟩ := weakDisk_boundary_semicircle_uniform he hγ heclosed
  exact ⟨R, hR, h F hp⟩

end PoincareConjecture.M65Boundary
