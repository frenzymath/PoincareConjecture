import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryCurvature
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryCollar
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace





theorem exists_subordinate_uniform_subdivision {ι : Type*} {a b : ℝ}
    (hab : a < b) (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i))
    (hcover : Icc a b ⊆ ⋃ i, U i) :
    ∃ (N : ℕ), 0 < N ∧ ∃ tag : Fin N → ι,
      ∀ i : Fin N, Icc (a + (b - a) * (i : ℝ) / N)
        (a + (b - a) * ((i : ℝ) + 1) / N) ⊆ U (tag i) := by
  classical
  obtain ⟨d, hd, hsub⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hU hcover
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / d)
  have hNR : 0 < (N : ℝ) := (div_pos (sub_pos.mpr hab) hd).trans hN
  have hNpos : 0 < N := by exact_mod_cast hNR
  have hstep : (b - a) / N < d := by
    apply (div_lt_iff₀ hNR).mpr
    have hh := (div_lt_iff₀ hd).mp hN
    nlinarith only [hh]
  have hleft (i : Fin N) : a + (b - a) * (i : ℝ) / N ∈ Icc a b := by
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i.val
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    have hnonneg : 0 ≤ (b - a) * (i : ℝ) / N :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hab.le) hi0) hNR.le
    have hle : (b - a) * (i : ℝ) / N ≤ b - a := by
      apply (div_le_iff₀ hNR).mpr
      exact mul_le_mul_of_nonneg_left hiN (sub_nonneg.mpr hab.le)
    exact ⟨by linarith, by linarith⟩
  choose tag htag using fun i : Fin N => hsub _ (hleft i)
  refine ⟨N, hNpos, tag, ?_⟩
  intro i t ht
  apply htag i
  rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  have hwidth :
      (a + (b - a) * ((i : ℝ) + 1) / N) - (a + (b - a) * (i : ℝ) / N) =
        (b - a) / N := by ring
  exact (sub_le_sub_right ht.2 _).trans_lt (hwidth ▸ hstep)





theorem boundaryCoordinate_angular_radius (a t h : ℝ) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    e (boundaryCoordinate (e.symm (Proofs.M58.angularPoint a))
      ((t : ℂ) + (h : ℂ) * I)) =
      Real.exp (-h) • Proofs.M58.angularPoint (t + a) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have hangle (s : ℝ) : e.symm (Proofs.M58.angularPoint s) =
      Complex.exp ((s : ℂ) * I) := by
    rw [Complex.exp_ofReal_mul_I]
    rfl
  apply e.symm.injective
  change e.symm (e _) = e.symm (Real.exp (-h) • Proofs.M58.angularPoint (t + a))
  rw [e.symm_apply_apply, map_smul, hangle, hangle]
  change Complex.exp ((a : ℂ) * I) *
    Complex.exp (I * ((t : ℂ) + (h : ℂ) * I)) = _
  rw [show I * ((t : ℂ) + (h : ℂ) * I) = (-h : ℝ) + (t : ℂ) * I by
    push_cast
    linear_combination (h : ℂ) * I_mul_I]
  rw [Complex.exp_add, ← Complex.ofReal_exp, ofReal_add, add_mul, Complex.exp_add]
  change Complex.exp ((a : ℂ) * I) *
    ((Real.exp (-h) : ℂ) * Complex.exp ((t : ℂ) * I)) =
      (Real.exp (-h) : ℂ) *
        (Complex.exp ((t : ℂ) * I) * Complex.exp ((a : ℂ) * I))
  ring

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}







theorem exists_angular_collar (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ∀ s, W (periodicFreeLoop gamma s) = M65Filling.loopCurvature connection gamma s)
    (a : ℝ) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let x := Proofs.M58.angularPoint a
    let p := e.symm x
    let P := e ∘ boundaryCoordinate p
    let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ P
    let B := fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
      (W (S.disk.map (Proofs.M58.angularPoint theta)))
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r d C : ℝ) (F : ℂ → LoopAmbient × LoopAmbient),
      0 < r ∧ 0 < d ∧ d < r / 4 ∧ 0 ≤ C ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      ContDiffOn ℝ 1 H K ∧ ContinuousOn F K ∧ ContDiffOn ℝ 1 F U ∧
      MemLp (fun z => fderiv ℝ F z 1) 2 (volume.restrict U) ∧
      (∀ z ∈ K, ∀ w ∈ K, ‖F z - F w‖ ≤ C * Real.sqrt ‖z - w‖) ∧
      (∀ z ∈ U,
        fderiv ℝ (fun w => Real.log (S.conformalFactor (e w)))
            (boundaryCoordinate p z) (boundaryCoordinate p z) / 2 ≤
          gE.inner (H z) (covariantDerivativeAlongMap DE H (fun w => (F w).1) z 1)
            (F z).2 - 1) ∧
      ∀ t ∈ Icc (-d) d,
        ContDiffAt ℝ 1 (fun s : ℝ => (F (s : ℂ)).1) t ∧
        gE.inner (H (t : ℂ))
          (deriv (fun s : ℝ => (F (s : ℂ)).1) t +
            connectionCoefficient DE (H (t : ℂ))
              (fderivWithin ℝ H K (t : ℂ) 1) (F (t : ℂ)).1) (F (t : ℂ)).2 =
          -B (t + a) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let x := Proofs.M58.angularPoint a
  let p := e.symm x
  let P := e ∘ boundaryCoordinate p
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ P
  have hx : ‖x‖ = 1 := Proofs.M58.norm_angularPoint a
  have hperiodic : periodicFreeLoop gamma = gamma ∘ m65LoopAngular := by
    funext t
    exact gamma.boundary (m65LoopAngular t)
  obtain ⟨gE, DE, r, m, Q, hr, hm, hP, hsource, hH, _hHi, hmetric, _hnorm,
      _hQ, _hQ1, _hQne, hfactor, hF, hF1, hunit, hDF, _hDFI, hholder, hradial⟩ :=
    S.boundary_branch_radial_connection hinj (hperiodic ▸ hsmooth)
      (hperiodic ▸ hregular) hx
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
  obtain ⟨C, hC, hbound⟩ := hholder
  have hboundary := S.boundary_connection_curvature_of_frame hsmooth hregular hx
    gE DE hr hm Q W hW hP hsource hH hmetric hfactor hF (fun z hz => (hunit z hz).1)
  obtain ⟨eta, heta, hetasub⟩ := Metric.mem_nhds_iff.mp hboundary
  let d := min (r / 8) (eta / 2)
  have hd : 0 < d := lt_min (by positivity) (half_pos heta)
  have hdr : d < r / 4 := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨gE, DE, r, d, C, F, hr, hd, hdr, hC, hH, hF, hF1, hDF, hbound, hradial, ?_⟩
  intro t ht
  have hteta : t ∈ ball (0 : ℝ) eta := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hh := hetasub hteta
  change ContDiffAt ℝ 1 (fun s : ℝ => (F (s : ℂ)).1) t ∧
    gE.inner (H (t : ℂ))
      (deriv (fun s : ℝ => (F (s : ℂ)).1) t +
        connectionCoefficient DE (H (t : ℂ))
          (fderivWithin ℝ H K (t : ℂ) 1) (F (t : ℂ)).1) (F (t : ℂ)).2 =
      -g.inner (S.disk.map (P (t : ℂ))) (W (S.disk.map (P (t : ℂ))))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
          (P (t : ℂ)) (P (t : ℂ))) at hh
  have hPangle : P (t : ℂ) = Proofs.M58.angularPoint (t + a) := by
    simpa only [P, p, x, Function.comp_apply, ofReal_zero, zero_mul, add_zero,
      neg_zero, Real.exp_zero, one_smul]
      using boundaryCoordinate_angular_radius a t 0
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact congrArg (fun y : LoopPlane => -g.inner (S.disk.map y) (W (S.disk.map y))
    (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet y y)) hPangle

end PoincareConjecture.M65MinimalDisk
