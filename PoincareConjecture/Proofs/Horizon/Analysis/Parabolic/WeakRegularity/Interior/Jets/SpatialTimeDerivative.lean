import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialJetAlgebra
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakDivergence

open Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem weak_time_pairing_of_forcing
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u f : Spacetime n → ℝ}
    (hu : LocallyIntegrableOn u U volume) (hf : LocallyIntegrableOn f U volume)
    {g : Fin n → Spacetime n → ℝ} {H : Fin n → Fin n → Spacetime n → ℝ}
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hH : ∀ i j, LocallyIntegrableOn (H i j) U volume)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y)
    (hgweak : ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y in U, φ y * g i y) = -(∫ y in U, spatialDeriv i φ y * u y))
    (hHweak : ∀ i j (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y in U, φ y * H i j y) = -(∫ y in U, spatialDeriv i φ y * g j y))
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y in U, φ y * (f y + (∑ i, ∑ j, C.principal i j y * H i j y) -
      (∑ i, C.drift i y * g i y) - C.zeroth y * u y)) =
      -(∫ y in U, timeDeriv φ y * u y) := by
  let T := fun y => f y + (∑ i, ∑ j, C.principal i j y * H i j y) -
    (∑ i, C.drift i y * g i y) - C.zeroth y * u y
  change (∫ y in U, φ y * T y) = _
  have smooth {a : Spacetime n → ℝ} (ha : ContDiffOn ℝ ∞ a U)
      (hs : tsupport a ⊆ U) : ContDiff ℝ ∞ a := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport a
    · exact (ha y (hs hy)).contDiffAt (hU.mem_nhds (hs hy))
    · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
  have integ {a ψ : Spacetime n → ℝ} (hal : LocallyIntegrableOn a U volume)
      (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
      Integrable (fun y => a y * ψ y) (volume.restrict U) := by
    have hi : Integrable (fun y => a y * ψ y) := by
      apply (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_right a ψ).trans (subset_tsupport ψ))).mp
      exact (hal.integrableOn_compact_subset hψU hψc).mul_continuousOn
        hψ.continuous.continuousOn hψc
    exact hi.integrableOn
  let A := fun i j y => C.principal i j y * φ y
  let B := fun i y => C.drift i y * φ y
  let Z := fun y => C.zeroth y * φ y
  have hAc (i j) : HasCompactSupport (A i j) := hφc.mul_left
  have hAU (i j) : tsupport (A i j) ⊆ U := tsupport_mul_subset_right.trans hφU
  have hA (i j) : ContDiff ℝ ∞ (A i j) :=
    smooth ((hC.1 i j).mul hφ.contDiffOn) (hAU i j)
  have hDA (i j) : ContDiff ℝ ∞ (spatialDeriv i (A i j)) :=
    ((hA i j).fderiv_right (by simp)).clm_apply contDiff_const
  have hDAc (i j) : HasCompactSupport (spatialDeriv i (A i j)) := (hAc i j).fderiv_apply ℝ _
  have hDAU (i j) : tsupport (spatialDeriv i (A i j)) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans (hAU i j)
  have hBc (i) : HasCompactSupport (B i) := hφc.mul_left
  have hBU (i) : tsupport (B i) ⊆ U := tsupport_mul_subset_right.trans hφU
  have hB (i) : ContDiff ℝ ∞ (B i) := smooth ((hC.2.1 i).mul hφ.contDiffOn) (hBU i)
  have hZc : HasCompactSupport Z := hφc.mul_left
  have hZU : tsupport Z ⊆ U := tsupport_mul_subset_right.trans hφU
  have hZ : ContDiff ℝ ∞ Z := smooth (hC.2.2.mul hφ.contDiffOn) hZU
  have hDt : ContDiff ℝ ∞ (timeDeriv φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDtc : HasCompactSupport (timeDeriv φ) := hφc.fderiv_apply ℝ (0, 1)
  have hDtU : tsupport (timeDeriv φ) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans hφU
  have iT := integ hu hDt hDtc hDtU
  have iA (i j) := integ (hg j) (hDA i j) (hDAc i j) (hDAU i j)
  have iH (i j) := integ (hH i j) (hA i j) (hAc i j) (hAU i j)
  have iB (i) := integ (hg i) (hB i) (hBc i) (hBU i)
  have iZ := integ hu hZ hZc hZU
  have iF := integ hf hφ hφc hφU
  have iAs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => iA i j))
  have iHs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => iH i j))
  have iBs := integrable_finsetSum Finset.univ (fun i _ => iB i)
  have hHp (i j) : (∫ y in U, g j y * spatialDeriv i (A i j) y) =
      -(∫ y in U, H i j y * A i j y) := by
    have hh : (∫ y in U, H i j y * A i j y) =
        -(∫ y in U, g j y * spatialDeriv i (A i j) y) := by
      simpa only [mul_comm] using hHweak i j (A i j) (hA i j) (hAc i j) (hAU i j)
    linarith only [hh]
  have hsrc : (∫ y, φ y * f y) = ∫ y in U, f y * φ y := by
    symm
    calc
      _ = ∫ y, f y * φ y := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφU h)), mul_zero])
      _ = _ := by apply integral_congr_ae; filter_upwards [] with y; exact mul_comm _ _
  have he := ((first_order_pairing_eq_adjoint hU hC hu hg
    hgweak hφ hφc hφU).trans (hforce φ hφ hφc hφU)).trans hsrc
  change (∫ y in U, -u y * timeDeriv φ y + (∑ i, ∑ j, g j y * spatialDeriv i (A i j) y) +
    (∑ i, g i y * B i y) + u y * Z y) = ∫ y in U, f y * φ y at he
  have he1 := integral_add ((iT.neg.add iAs).add iBs) iZ
  have he2 := integral_add (iT.neg.add iAs) iBs
  have he3 := integral_add iT.neg iAs
  simp only [Pi.add_apply, Pi.neg_apply] at he1 he2 he3
  simp only [neg_mul] at he
  rw [he1, he2, he3, integral_neg,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => iA i j)),
    integral_finsetSum _ (fun i _ => iB i)] at he
  simp_rw [integral_finsetSum _ (fun j _ => iA _ j), hHp, Finset.sum_neg_distrib] at he
  have hTp : (∫ y in U, φ y * T y) = (∫ y in U, f y * φ y) +
      (∑ i, ∑ j, ∫ y in U, H i j y * A i j y) -
      (∑ i, ∫ y in U, g i y * B i y) - ∫ y in U, u y * Z y := by
    calc
      _ = ∫ y in U, f y * φ y + (∑ i, ∑ j, H i j y * A i j y) -
          (∑ i, g i y * B i y) - u y * Z y := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [T, A, B, Z, mul_add, mul_sub, Finset.mul_sum,
          mul_left_comm, mul_comm]
      _ = _ := by
        have h1 := integral_sub ((iF.add iHs).sub iBs) iZ
        have h2 := integral_sub (iF.add iHs) iBs
        have h3 := integral_add iF iHs
        simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
        rw [h1, h2, h3,
          integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => iH i j)),
          integral_finsetSum _ (fun i _ => iB i)]
        simp_rw [integral_finsetSum _ (fun j _ => iH _ j)]
  have htcomm : (∫ y in U, timeDeriv φ y * u y) = ∫ y in U, u y * timeDeriv φ y := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact mul_comm _ _
  rw [hTp, htcomm]
  linarith only [he]

theorem exists_spatial_jet_weak_time_derivative
    {n k : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u f : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U (k + 2) u) (hf : HasSpatialL2Jet U k f)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y) :
    ∃ T : Spacetime n → ℝ, HasSpatialL2Jet U k T ∧
      ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ y in U, φ y * T y) = -(∫ y in U, timeDeriv φ y * u y) := by
  have ha (i j) : ContDiff ℝ ∞ (C.principal i j) := contDiffOn_univ.mp (hC.1 i j)
  have hb (i) : ContDiff ℝ ∞ (C.drift i) := contDiffOn_univ.mp (hC.2.1 i)
  have hc : ContDiff ℝ ∞ C.zeroth := contDiffOn_univ.mp hC.2.2
  have hCU : C.IsSmoothOn U :=
    ⟨fun i j => (ha i j).contDiffOn, fun i => (hb i).contDiffOn, hc.contDiffOn⟩
  have huk : HasSpatialL2Jet U k u := hu.of_le (by omega)
  have hul := hu.locallyIntegrableOn
  obtain ⟨hum, g, hg, hgw⟩ := hu
  have hhex (j : Fin n) : ∃ H : Fin n → Spacetime n → ℝ,
      (∀ i, HasSpatialL2Jet U k (H i)) ∧
      ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        (∫ y in U, φ y * H i y) = -(∫ y in U, spatialDeriv i φ y * g j y) := (hg j).2
  choose H hH hHw using hhex
  let T := fun y => f y + (∑ i, ∑ j, C.principal i j y * H j i y) -
    (∑ i, C.drift i y * g i y) - C.zeroth y * u y
  have hTA : HasSpatialL2Jet U k (fun y => ∑ i, ∑ j, C.principal i j y * H j i y) :=
    HasSpatialL2Jet.sum Finset.univ (fun i _ => HasSpatialL2Jet.sum Finset.univ
      (fun j _ => (hH j i).mul_smooth hU (ha i j) (hprincipalc i j)))
  have hTB : HasSpatialL2Jet U k (fun y => ∑ i, C.drift i y * g i y) :=
    HasSpatialL2Jet.sum Finset.univ
      (fun i _ => (hg i).lower.mul_smooth hU (hb i) (hdriftc i))
  have hTZ : HasSpatialL2Jet U k (fun y => C.zeroth y * u y) :=
    huk.mul_smooth hU hc hzerothc
  refine ⟨T, ((hf.add hTA).sub hTB).sub hTZ, ?_⟩
  intro φ hφ hφc hφU
  exact weak_time_pairing_of_forcing hU hCU hul hf.locallyIntegrableOn
    (fun i => (hg i).locallyIntegrableOn) (fun i j => (hH j i).locallyIntegrableOn)
    hforce hgw (fun i j => hHw j i) hφ hφc hφU

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
