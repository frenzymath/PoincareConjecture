import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RawAnnulusFiberTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff Manifold

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

local instance : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
  ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne

variable {m : ℕ}



theorem interiorCurve_vertical_trace_pointwise_vector
    {f d : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b0 b1 : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f mu) (hd2 : MemLp d 2 mu)
    (hfs : ContDiffOn ℝ 1 f S)
    (hdeq : d =ᵐ[mu] (fun p => fderiv ℝ f p e1))
    (havg0 : ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
      f (annulusPoint x s) + (s - 1) • d (annulusPoint x s)) = b0 x)
    (havg1 : ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
      f (annulusPoint x s) + s • d (annulusPoint x s)) = b1 x) :
    ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t) := by
  have hu : Integrable f mu := hf
  have hd : Integrable d mu := hd2.integrable (by norm_num)
  have hprodd := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hd
  have hprod0 := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable
    (hu.add (m64Annulus_continuous_smul_integrable hd (by fun_prop :
      Continuous (fun p : LoopPlane => (p 1 - 1 : ℝ)))))
  have hprod1 := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable
    (hu.add (m64Annulus_continuous_smul_integrable hd (by fun_prop :
      Continuous (fun p : LoopPlane => (p 1 : ℝ)))))
  have hcoord (j : Fin m) : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      (EuclideanSpace.proj (𝕜 := ℝ) j) (f (annulusPoint x s)) -
          (EuclideanSpace.proj (𝕜 := ℝ) j) (b0 x) =
            ∫ t in (0 : ℝ)..s,
              (EuclideanSpace.proj (𝕜 := ℝ) j) (d (annulusPoint x t)) ∧
      (EuclideanSpace.proj (𝕜 := ℝ) j) (b1 x) -
          (EuclideanSpace.proj (𝕜 := ℝ) j) (f (annulusPoint x s)) =
            ∫ t in s..(1 : ℝ),
              (EuclideanSpace.proj (𝕜 := ℝ) j) (d (annulusPoint x t)) := by
    let P := EuclideanSpace.proj (𝕜 := ℝ) j
    have hf' : Integrable (fun p => P (f p)) mu := P.integrable_comp hf
    have hd2' : MemLp (fun p => P (d p)) 2 mu := P.comp_memLp' hd2
    have hfs' : ContDiffOn ℝ 1 (fun p => P (f p)) S :=
      P.contDiff.comp_contDiffOn hfs
    have hdeq' : (fun p => P (d p)) =ᵐ[mu]
        (fun p => fderiv ℝ (fun q => P (f q)) p e1) := by
      filter_upwards [hdeq, ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
      have hfd := fderiv_comp p P.differentiableAt
        ((hfs.contDiffAt (isOpen_interior.mem_nhds hpS)).differentiableAt (by simp))
      rw [P.fderiv] at hfd
      exact (congrArg P hp).trans (congrArg (fun L => L e1) hfd).symm
    have havg0' : ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
        P (f (annulusPoint x s)) + (s - 1) * P (d (annulusPoint x s))) = P (b0 x) := by
      filter_upwards [havg0, hprod0.prod_right_ae] with x hx hxi
      change IntegrableOn (fun s => f (annulusPoint x s) +
        (s - 1) • d (annulusPoint x s)) (Icc (0 : ℝ) 1) volume at hxi
      have hxj := congrArg P hx
      calc
        _ = ∫ s in Icc (0 : ℝ) 1,
            P (f (annulusPoint x s) + (s - 1) • d (annulusPoint x s)) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun s => by simp [smul_eq_mul]
        _ = P (∫ s in Icc (0 : ℝ) 1,
            f (annulusPoint x s) + (s - 1) • d (annulusPoint x s)) :=
          P.integral_comp_comm hxi
        _ = P (b0 x) := hxj
    have havg1' : ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
        P (f (annulusPoint x s)) + s * P (d (annulusPoint x s))) = P (b1 x) := by
      filter_upwards [havg1, hprod1.prod_right_ae] with x hx hxi
      change IntegrableOn (fun s => f (annulusPoint x s) +
        s • d (annulusPoint x s)) (Icc (0 : ℝ) 1) volume at hxi
      have hxj := congrArg P hx
      calc
        _ = ∫ s in Icc (0 : ℝ) 1,
            P (f (annulusPoint x s) + s • d (annulusPoint x s)) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun s => by simp [smul_eq_mul]
        _ = P (∫ s in Icc (0 : ℝ) 1,
            f (annulusPoint x s) + s • d (annulusPoint x s)) :=
          P.integral_comp_comm hxi
        _ = P (b1 x) := hxj
    exact interiorCurve_vertical_trace_pointwise hf' hd2' hfs' hdeq'
      havg0' havg1'
  filter_upwards [ae_all_iff.mpr hcoord, hprodd.prod_right_ae] with x hx hdx
  change IntegrableOn (fun t => d (annulusPoint x t)) (Icc (0 : ℝ) 1) volume at hdx
  have hdxI : IntervalIntegrable (fun t => d (annulusPoint x t)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hdx
  intro s hs
  constructor
  · apply PiLp.ext
    intro j
    let P := EuclideanSpace.proj (𝕜 := ℝ) j
    have hdx_left : IntervalIntegrable (fun t => d (annulusPoint x t)) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1.le).mpr
        (hdx.mono_set (Icc_subset_Icc le_rfl hs.2.le))
    change P (f (annulusPoint x s)) - P (b0 x) =
      P (∫ t in (0 : ℝ)..s, d (annulusPoint x t))
    rw [← P.intervalIntegral_comp_comm hdx_left]
    exact (hx j s hs).1
  · apply PiLp.ext
    intro j
    let P := EuclideanSpace.proj (𝕜 := ℝ) j
    have hdx_right : IntervalIntegrable (fun t => d (annulusPoint x t)) volume s 1 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2.le).mpr
        (hdx.mono_set (Icc_subset_Icc hs.1.le le_rfl))
    change P (b1 x) - P (f (annulusPoint x s)) =
      P (∫ t in s..(1 : ℝ), d (annulusPoint x t))
    rw [← P.intervalIntegral_comp_comm hdx_right]
    exact (hx j s hs).2

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane}
  {c0 c1 : ℝ → M} {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

open Poincare.Analysis.Sobolev.Weak




theorem M64FreeWeakPhaseAnnulus.raw_vertical_trace_pointwise
    (L : M64FreeWeakPhaseAnnulus (n := n) e R
      c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S)
    (h0 : Integrable (e ∘ (c0 ∘ L.label0)) nu)
    (h1 : Integrable (e ∘ (c1 ∘ L.label1)) nu) :
    ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      e (L.annulus.map (annulusPoint x s)) - e (c0 (L.label0 x)) =
        ∫ t in (0 : ℝ)..s, (L.annulus.column 1) (annulusPoint x t) ∧
      e (c1 (L.label1 x)) - e (L.annulus.map (annulusPoint x s)) =
        ∫ t in s..(1 : ℝ), (L.annulus.column 1) (annulusPoint x t) := by
  have hf : Integrable (fun p => e (L.annulus.map p)) mu :=
    L.annulus.observed_memLp.integrable (by norm_num)
  have hd2 : MemLp (L.annulus.column 1) 2 mu := Lp.memLp _
  have hfs : ContDiffOn ℝ 1 (fun p => e (L.annulus.map p)) S := by
    intro p hp
    exact (contMDiffAt_iff_contDiffAt.mp ((he _).comp p
      (hA.contMDiffAt (isOpen_interior.mem_nhds hp)))).contDiffWithinAt
  have hdeq : (L.annulus.column 1 : LoopPlane → EuclideanSpace ℝ (Fin m)) =ᵐ[mu]
      (fun p => fderiv ℝ (fun q => e (L.annulus.map q)) p e1) := by
    simpa only [Function.comp_def] using
      (L.annulus.classical_columns_of_contMDiffOn he hA 1)
  have havg := L.annulus.radial_trace_averages h0 h1
  exact interiorCurve_vertical_trace_pointwise_vector hf hd2 hfs hdeq
    (havg.mono fun x hx => by simpa only [Function.comp_def] using hx.1)
    (havg.mono fun x hx => by simpa only [Function.comp_def] using hx.2)





theorem interiorCurve_vertical_trace_l2_control
    {f d : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b0 b1 : ℝ → EuclideanSpace ℝ (Fin m)}
    (hd2 : MemLp d 2 mu)
    (hpoint : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t)) :
    ∀ s ∈ Ioo (0 : ℝ) 1,
      (MemLp (fun x => f (annulusPoint x s) - b0 x) 2 nu ∧
      (∫ x in Icc (0 : ℝ) curvePeriod,
          ‖f (annulusPoint x s) - b0 x‖ ^ 2) ≤
        s * ∫ p in S, ‖d p‖ ^ 2) ∧
      (MemLp (fun x => f (annulusPoint x s) - b1 x) 2 nu ∧
      (∫ x in Icc (0 : ℝ) curvePeriod,
          ‖f (annulusPoint x s) - b1 x‖ ^ 2) ≤
        (1 - s) * ∫ p in S, ‖d p‖ ^ 2) := by
  have hdnormsq : Integrable (fun p => ‖d p‖ ^ 2) mu :=
    hd2.norm.integrable_sq
  have hprodd := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable
    (hd2.integrable (by norm_num))
  have hprodnorm := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hdnormsq
  have hfull : Integrable (fun x => ∫ t in Icc (0 : ℝ) 1,
      ‖d (annulusPoint x t)‖ ^ 2) nu := by
    have h := hprodnorm.integral_prod_left
    change Integrable (fun x => ∫ t in Icc (0 : ℝ) 1,
      ‖d (annulusPoint x t)‖ ^ 2) nu at h
    exact h
  have hbound_lower (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (x : ℝ)
      (hxd : IntegrableOn (fun t => d (annulusPoint x t))
        (Icc (0 : ℝ) 1) volume)
      (hxd2 : IntegrableOn (fun t => ‖d (annulusPoint x t)‖ ^ 2)
        (Icc (0 : ℝ) 1) volume) :
      ‖∫ t in (0 : ℝ)..s, d (annulusPoint x t)‖ ^ 2 ≤
        s * ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := by
    have hmemI : MemLp (fun t => d (annulusPoint x t)) 2
        (volume.restrict (Icc (0 : ℝ) 1)) :=
      (memLp_two_iff_integrable_sq_norm hxd.aestronglyMeasurable).mpr hxd2
    have hmem : MemLp (fun t => d (annulusPoint x t)) 2
        (volume.restrict (Ioc (0 : ℝ) s)) :=
      hmemI.mono_measure (Measure.restrict_mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hs.2.le)) le_rfl)
    have hcs := M64Uniformization.scalar_integral_mul_sq_le
      (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t => ‖d (annulusPoint x t)‖)
      (memLp_const 1) hmem.norm
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hs.1.le
      (f := fun t => d (annulusPoint x t))
    have hnormIoc : ‖∫ t in Ioc (0 : ℝ) s, d (annulusPoint x t)‖ ≤
        ∫ t in Ioc (0 : ℝ) s, ‖d (annulusPoint x t)‖ := by
      simpa only [intervalIntegral.integral_of_le hs.1.le] using hnorm
    have hnorm' : ‖∫ t in (0 : ℝ)..s, d (annulusPoint x t)‖ ≤
        ∫ t in Ioc (0 : ℝ) s, ‖d (annulusPoint x t)‖ := by
      calc
        _ = ‖∫ t in Ioc (0 : ℝ) s, d (annulusPoint x t)‖ := by
          rw [intervalIntegral.integral_of_le hs.1.le]
        _ ≤ _ := hnormIoc
    have hmono : (∫ t in Ioc (0 : ℝ) s,
        ‖d (annulusPoint x t)‖ ^ 2) ≤
        ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := by
      exact setIntegral_mono_set hxd2 (Eventually.of_forall (fun _ => sq_nonneg _))
        (ae_of_all volume (fun t ht => (Ioc_subset_Icc_self.trans
          (Icc_subset_Icc le_rfl hs.2.le)) ht))
    have hcs' : (∫ t in Ioc (0 : ℝ) s,
        ‖d (annulusPoint x t)‖) ^ 2 ≤
        s * ∫ t in Ioc (0 : ℝ) s, ‖d (annulusPoint x t)‖ ^ 2 := by
      simpa [MeasureTheory.integral_const, hs.1.le] using hcs
    have hnorm' : ‖∫ t in (0 : ℝ)..s, d (annulusPoint x t)‖ ^ 2 ≤
        (∫ t in Ioc (0 : ℝ) s, ‖d (annulusPoint x t)‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))).mpr hnorm'
    exact hnorm'.trans (hcs'.trans (mul_le_mul_of_nonneg_left hmono hs.1.le))
  have hbound_upper (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (x : ℝ)
      (hxd : IntegrableOn (fun t => d (annulusPoint x t))
        (Icc (0 : ℝ) 1) volume)
      (hxd2 : IntegrableOn (fun t => ‖d (annulusPoint x t)‖ ^ 2)
        (Icc (0 : ℝ) 1) volume) :
      ‖∫ t in s..(1 : ℝ), d (annulusPoint x t)‖ ^ 2 ≤
        (1 - s) * ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := by
    have hmemI : MemLp (fun t => d (annulusPoint x t)) 2
        (volume.restrict (Icc (0 : ℝ) 1)) :=
      (memLp_two_iff_integrable_sq_norm hxd.aestronglyMeasurable).mpr hxd2
    have hmem : MemLp (fun t => d (annulusPoint x t)) 2
        (volume.restrict (Ioc s (1 : ℝ))) :=
      hmemI.mono_measure (Measure.restrict_mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1.le le_rfl)) le_rfl)
    have hcs := M64Uniformization.scalar_integral_mul_sq_le
      (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t => ‖d (annulusPoint x t)‖)
      (memLp_const 1) hmem.norm
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hs.2.le
      (f := fun t => d (annulusPoint x t))
    have hnormIoc : ‖∫ t in Ioc s (1 : ℝ), d (annulusPoint x t)‖ ≤
        ∫ t in Ioc s (1 : ℝ), ‖d (annulusPoint x t)‖ := by
      simpa only [intervalIntegral.integral_of_le hs.2.le] using hnorm
    have hnorm' : ‖∫ t in s..(1 : ℝ), d (annulusPoint x t)‖ ≤
        ∫ t in Ioc s (1 : ℝ), ‖d (annulusPoint x t)‖ := by
      calc
        _ = ‖∫ t in Ioc s (1 : ℝ), d (annulusPoint x t)‖ := by
          rw [intervalIntegral.integral_of_le hs.2.le]
        _ ≤ _ := hnormIoc
    have hmono : (∫ t in Ioc s (1 : ℝ),
        ‖d (annulusPoint x t)‖ ^ 2) ≤
        ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := by
      exact setIntegral_mono_set hxd2 (Eventually.of_forall (fun _ => sq_nonneg _))
        (ae_of_all volume (fun t ht => (Ioc_subset_Icc_self.trans
          (Icc_subset_Icc hs.1.le le_rfl)) ht))
    have hcs' : (∫ t in Ioc s (1 : ℝ),
        ‖d (annulusPoint x t)‖) ^ 2 ≤
        (1 - s) * ∫ t in Ioc s (1 : ℝ), ‖d (annulusPoint x t)‖ ^ 2 := by
      simpa [MeasureTheory.integral_const, hs.2.le] using hcs
    have hnorm' : ‖∫ t in s..(1 : ℝ), d (annulusPoint x t)‖ ^ 2 ≤
        (∫ t in Ioc s (1 : ℝ), ‖d (annulusPoint x t)‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))).mpr hnorm'
    exact hnorm'.trans (hcs'.trans (mul_le_mul_of_nonneg_left hmono
      (sub_nonneg.mpr hs.2.le)))
  intro s hs
  have hleft : (∫ x in Icc (0 : ℝ) curvePeriod,
      ‖f (annulusPoint x s) - b0 x‖ ^ 2) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        ‖∫ t in (0 : ℝ)..s, d (annulusPoint x t)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hpoint] with x hx
    rw [(hx s hs).1]
  have hright : (∫ x in Icc (0 : ℝ) curvePeriod,
      ‖f (annulusPoint x s) - b1 x‖ ^ 2) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        ‖∫ t in s..(1 : ℝ), d (annulusPoint x t)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hpoint] with x hx
    have heq := (hx s hs).2
    have heq' : f (annulusPoint x s) - b1 x =
        -∫ t in s..(1 : ℝ), d (annulusPoint x t) := by
      calc
        _ = -(b1 x - f (annulusPoint x s)) := by abel
        _ = -∫ t in s..(1 : ℝ), d (annulusPoint x t) := by rw [heq]
    rw [heq', norm_neg]
  have hxi : ∀ᵐ x ∂nu, IntegrableOn (fun t => d (annulusPoint x t))
      (Icc (0 : ℝ) 1) volume := by
    simpa only [Function.comp_apply, IntegrableOn] using hprodd.prod_right_ae
  have hxi2 : ∀ᵐ x ∂nu, IntegrableOn (fun t => ‖d (annulusPoint x t)‖ ^ 2)
      (Icc (0 : ℝ) 1) volume := by
    simpa only [Function.comp_apply, IntegrableOn] using hprodnorm.prod_right_ae
  constructor
  · have hprodL : Integrable (d ∘ fun q => annulusPoint q.1 q.2)
        ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
          (volume.restrict (Ioc (0 : ℝ) s))) :=
      hprodd.mono_measure (Measure.prod_mono le_rfl
        (Measure.restrict_mono (μ := volume) (s := Ioc (0 : ℝ) s)
          (s' := Icc (0 : ℝ) 1)
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hs.2.le)) le_rfl))
    have hprimL : Integrable (fun x => ∫ t in Ioc (0 : ℝ) s,
        d (annulusPoint x t)) nu := by
      have h := hprodL.integral_prod_left
      change Integrable (fun x => ∫ t in Ioc (0 : ℝ) s,
        d (annulusPoint x t)) nu at h
      exact h
    have hbound0 : ∀ᵐ x ∂nu,
        ‖∫ t in Ioc (0 : ℝ) s, d (annulusPoint x t)‖ ^ 2 ≤
          s * ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := by
      filter_upwards [hxi, hxi2] with x hxd hxd2
      rw [← intervalIntegral.integral_of_le hs.1.le]
      exact hbound_lower s hs x hxd hxd2
    have hprimLsq : Integrable (fun x =>
        ‖∫ t in Ioc (0 : ℝ) s, d (annulusPoint x t)‖ ^ 2) nu := by
      have hG := hfull.const_mul s
      apply hG.mono'
      · have hm := hprimL.aestronglyMeasurable.norm.pow 2
        convert hm using 1
        ext x
        simp
      · filter_upwards [hbound0] with x hx
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg (‖∫ t in Ioc (0 : ℝ) s,
            d (annulusPoint x t)‖))] using hx
    have hmono := integral_mono_ae hprimLsq (hfull.const_mul s) hbound0
    have hprimLM := (memLp_two_iff_integrable_sq_norm
      hprimL.aestronglyMeasurable).mpr hprimLsq
    have htrace : (fun x => ∫ t in Ioc (0 : ℝ) s, d (annulusPoint x t)) =ᵐ[nu]
        (fun x => f (annulusPoint x s) - b0 x) := by
      filter_upwards [hpoint] with x hx
      simpa only [intervalIntegral.integral_of_le hs.1.le] using (hx s hs).1.symm
    refine ⟨MemLp.ae_eq htrace hprimLM, ?_⟩
    rw [hleft]
    simp only [intervalIntegral.integral_of_le hs.1.le]
    calc
      _ ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
          s * ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := hmono
      _ = s * ∫ x in Icc (0 : ℝ) curvePeriod,
          ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 :=
        integral_const_mul _ _
      _ = s * ∫ p in S, ‖d p‖ ^ 2 := by
        rw [m64AnnulusInteriorIntegral_eq_iterated_integrable _ hdnormsq]
  · have hprodR : Integrable (d ∘ fun q => annulusPoint q.1 q.2)
        ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
          (volume.restrict (Ioc s (1 : ℝ)))) :=
      hprodd.mono_measure (Measure.prod_mono le_rfl
        (Measure.restrict_mono (μ := volume) (s := Ioc s (1 : ℝ))
          (s' := Icc (0 : ℝ) 1)
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1.le le_rfl)) le_rfl))
    have hprimR : Integrable (fun x => ∫ t in Ioc s (1 : ℝ),
        d (annulusPoint x t)) nu := by
      have h := hprodR.integral_prod_left
      change Integrable (fun x => ∫ t in Ioc s (1 : ℝ),
        d (annulusPoint x t)) nu at h
      exact h
    have hbound1 : ∀ᵐ x ∂nu,
        ‖∫ t in Ioc s (1 : ℝ), d (annulusPoint x t)‖ ^ 2 ≤
          (1 - s) * ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := by
      filter_upwards [hxi, hxi2] with x hxd hxd2
      rw [← intervalIntegral.integral_of_le hs.2.le]
      exact hbound_upper s hs x hxd hxd2
    have hprimRsq : Integrable (fun x =>
        ‖∫ t in Ioc s (1 : ℝ), d (annulusPoint x t)‖ ^ 2) nu := by
      have hG := hfull.const_mul (1 - s)
      apply hG.mono'
      · have hm := hprimR.aestronglyMeasurable.norm.pow 2
        convert hm using 1
        ext x
        simp
      · filter_upwards [hbound1] with x hx
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg (‖∫ t in Ioc s (1 : ℝ),
            d (annulusPoint x t)‖))] using hx
    have hmono := integral_mono_ae hprimRsq (hfull.const_mul (1 - s)) hbound1
    have hprimRM := (memLp_two_iff_integrable_sq_norm
      hprimR.aestronglyMeasurable).mpr hprimRsq
    have htrace : (fun x => -(∫ t in Ioc s (1 : ℝ), d (annulusPoint x t))) =ᵐ[nu]
        (fun x => f (annulusPoint x s) - b1 x) := by
      filter_upwards [hpoint] with x hx
      rw [← intervalIntegral.integral_of_le hs.2.le, ← (hx s hs).2]
      abel
    refine ⟨MemLp.ae_eq htrace hprimRM.neg, ?_⟩
    rw [hright]
    simp only [intervalIntegral.integral_of_le hs.2.le]
    calc
      _ ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
          (1 - s) * ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 := hmono
      _ = (1 - s) * ∫ x in Icc (0 : ℝ) curvePeriod,
          ∫ t in Icc (0 : ℝ) 1, ‖d (annulusPoint x t)‖ ^ 2 :=
        integral_const_mul _ _
      _ = (1 - s) * ∫ p in S, ‖d p‖ ^ 2 := by
        rw [m64AnnulusInteriorIntegral_eq_iterated_integrable _ hdnormsq]




theorem interiorCurve_vertical_trace_l2_bounds
    {f d : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b0 b1 : ℝ → EuclideanSpace ℝ (Fin m)}
    (hd2 : MemLp d 2 mu)
    (hpoint : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t)) :
    ∀ s ∈ Ioo (0 : ℝ) 1,
      (∫ x in Icc (0 : ℝ) curvePeriod, ‖f (annulusPoint x s) - b0 x‖ ^ 2) ≤
        s * ∫ p in S, ‖d p‖ ^ 2 ∧
      (∫ x in Icc (0 : ℝ) curvePeriod, ‖f (annulusPoint x s) - b1 x‖ ^ 2) ≤
        (1 - s) * ∫ p in S, ‖d p‖ ^ 2 := by
  intro s hs
  have h := interiorCurve_vertical_trace_l2_control hd2 hpoint s hs
  exact ⟨h.1.2, h.2.2⟩




theorem interiorCurve_vertical_trace_memLp
    {f d : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b0 b1 : ℝ → EuclideanSpace ℝ (Fin m)}
    (hd2 : MemLp d 2 mu)
    (hpoint : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t)) :
    ∀ s ∈ Ioo (0 : ℝ) 1,
      MemLp (fun x => f (annulusPoint x s) - b0 x) 2 nu ∧
      MemLp (fun x => f (annulusPoint x s) - b1 x) 2 nu := by
  intro s hs
  have h := interiorCurve_vertical_trace_l2_control hd2 hpoint s hs
  exact ⟨h.1.1, h.2.1⟩

private theorem trace_eLpNorm_eq_sqrt {v : ℝ → EuclideanSpace ℝ (Fin m)}
    (hv : MemLp v 2 nu) :
    eLpNorm v 2 nu = ENNReal.ofReal (Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂nu)) := by
  have hsq : (eLpNorm v 2 nu).toReal ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂nu := by
    rw [← Lp.norm_toLp v hv, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    simp only [hx, real_inner_self_eq_norm_sq]
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hv.eLpNorm_lt_top.ne]




theorem interiorCurve_vertical_trace_square_tendsto
    {f d : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b0 b1 : ℝ → EuclideanSpace ℝ (Fin m)}
    (hd2 : MemLp d 2 mu)
    (hpoint : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t)) :
    Tendsto (fun s => ∫ x, ‖f (annulusPoint x s) - b0 x‖ ^ 2 ∂nu)
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun s => ∫ x, ‖f (annulusPoint x s) - b1 x‖ ^ 2 ∂nu)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hbound := interiorCurve_vertical_trace_l2_bounds hd2 hpoint
  constructor
  · have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun s : ℝ => s * ∫ p in S, ‖d p‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_mul] using hid.mul_const (∫ p in S, ‖d p‖ ^ 2)
    apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg
      (fun _ => sq_nonneg _))) ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with s hs
    exact (hbound s hs).1
  · have hid : Tendsto (fun s : ℝ => s) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun s : ℝ => (1 - s) * ∫ p in S, ‖d p‖ ^ 2)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa only [sub_self, zero_mul] using
        (hid.const_sub 1).mul_const (∫ p in S, ‖d p‖ ^ 2)
    apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg
      (fun _ => sq_nonneg _))) ?_ hlim
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with s hs
    exact (hbound s hs).2




theorem interiorCurve_vertical_trace_eLpNorm_tendsto
    {f d : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b0 b1 : ℝ → EuclideanSpace ℝ (Fin m)}
    (hd2 : MemLp d 2 mu)
    (hpoint : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t)) :
    Tendsto (fun s => eLpNorm (fun x => f (annulusPoint x s) - b0 x) 2 nu)
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun s => eLpNorm (fun x => f (annulusPoint x s) - b1 x) 2 nu)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hmem := interiorCurve_vertical_trace_memLp hd2 hpoint
  have hlim := interiorCurve_vertical_trace_square_tendsto hd2 hpoint
  constructor
  · have h := ENNReal.tendsto_ofReal hlim.1.sqrt
    simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at h
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with s hs
    exact (trace_eLpNorm_eq_sqrt (hmem s hs).1).symm
  · have h := ENNReal.tendsto_ofReal hlim.2.sqrt
    simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at h
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with s hs
    exact (trace_eLpNorm_eq_sqrt (hmem s hs).2).symm

private theorem observed_monotone_trace_memLp
    {b : ℝ → EuclideanSpace ℝ (Fin m)} {sigma : ℝ → ℝ}
    (hb : Continuous b) (hsigma : Monotone sigma) :
    MemLp (b ∘ sigma) 2 nu := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hb
    (s := Icc (sigma 0) (sigma curvePeriod))).isBounded.exists_norm_le
  apply MemLp.of_bound (hb.comp_aestronglyMeasurable
    hsigma.measurable.aestronglyMeasurable) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC _ (mem_image_of_mem b ⟨hsigma hx.1, hsigma hx.2⟩)





theorem M64FreeWeakPhaseAnnulus.raw_vertical_trace_l2_control
    (L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1)) :
    ∀ s ∈ Ioo (0 : ℝ) 1,
      (MemLp (fun x => e (L.annulus.map (annulusPoint x s)) -
          e (c0 (L.label0 x))) 2 nu ∧
        (∫ x, ‖e (L.annulus.map (annulusPoint x s)) - e (c0 (L.label0 x))‖ ^ 2 ∂nu) ≤
          s * ∫ p in S, ‖L.annulus.column 1 p‖ ^ 2) ∧
      (MemLp (fun x => e (L.annulus.map (annulusPoint x s)) -
          e (c1 (L.label1 x))) 2 nu ∧
        (∫ x, ‖e (L.annulus.map (annulusPoint x s)) - e (c1 (L.label1 x))‖ ^ 2 ∂nu) ≤
          (1 - s) * ∫ p in S, ‖L.annulus.column 1 p‖ ^ 2) := by
  have h0 := (observed_monotone_trace_memLp hc0 L.label0_monotone).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have h1 := (observed_monotone_trace_memLp hc1 L.label1_monotone).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  exact interiorCurve_vertical_trace_l2_control
    (f := fun p => e (L.annulus.map p))
    (b0 := fun x => e (c0 (L.label0 x))) (b1 := fun x => e (c1 (L.label1 x)))
    (Lp.memLp (L.annulus.column 1))
    (L.raw_vertical_trace_pointwise he hA h0 h1)




theorem M64FreeWeakPhaseAnnulus.raw_vertical_trace_square_tendsto
    (L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1)) :
    Tendsto (fun s => ∫ x, ‖e (L.annulus.map (annulusPoint x s)) -
      e (c0 (L.label0 x))‖ ^ 2 ∂nu) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun s => ∫ x, ‖e (L.annulus.map (annulusPoint x s)) -
      e (c1 (L.label1 x))‖ ^ 2 ∂nu) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have h0 := (observed_monotone_trace_memLp hc0 L.label0_monotone).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have h1 := (observed_monotone_trace_memLp hc1 L.label1_monotone).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  exact interiorCurve_vertical_trace_square_tendsto
    (f := fun p => e (L.annulus.map p))
    (b0 := fun x => e (c0 (L.label0 x))) (b1 := fun x => e (c1 (L.label1 x)))
    (Lp.memLp (L.annulus.column 1))
    (L.raw_vertical_trace_pointwise he hA h0 h1)




theorem M64FreeWeakPhaseAnnulus.raw_vertical_trace_strong
    (L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1)) :
    Tendsto (fun s => eLpNorm (fun x => e (L.annulus.map (annulusPoint x s)) -
      e (c0 (L.label0 x))) 2 nu) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun s => eLpNorm (fun x => e (L.annulus.map (annulusPoint x s)) -
      e (c1 (L.label1 x))) 2 nu) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have h0 := (observed_monotone_trace_memLp hc0 L.label0_monotone).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have h1 := (observed_monotone_trace_memLp hc1 L.label1_monotone).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  exact interiorCurve_vertical_trace_eLpNorm_tendsto
    (f := fun p => e (L.annulus.map p))
    (b0 := fun x => e (c0 (L.label0 x))) (b1 := fun x => e (c1 (L.label1 x)))
    (Lp.memLp (L.annulus.column 1))
    (L.raw_vertical_trace_pointwise he hA h0 h1)

end PoincareConjecture
