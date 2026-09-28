import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateSwap












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture





def m64BoundaryReflect (epsilon : ℝ) (u : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  (halfSpace 2).indicator u p + epsilon * (halfSpace 2).indicator u (reflect p)




theorem m64BoundaryReflect_memLp {u : LoopPlane → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p (volume.restrict (halfSpace 2))) (epsilon : ℝ) :
    MemLp (m64BoundaryReflect epsilon u) p volume := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  exact hi.add ((hi.comp_measurePreserving measurePreserving_reflect).const_mul epsilon)

private theorem integral_indicator_pair (u q : LoopPlane → ℝ) :
    (∫ x, (halfSpace 2).indicator u x * q x) = ∫ x in halfSpace 2, u x * q x := by
  rw [← integral_indicator isOpen_halfSpace.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ halfSpace 2 <;> simp [hx]






theorem m64BoundaryReflect_integral_of_one_le {u q : LoopPlane → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hu : MemLp u p (volume.restrict (halfSpace 2)))
    (hq : Continuous q) (hc : HasCompactSupport q) (epsilon : ℝ) :
    (∫ x, m64BoundaryReflect epsilon u x * q x) =
      ∫ x in halfSpace 2, u x * (q x + epsilon * q (reflect x)) := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have hqr : Continuous (q ∘ reflect) := hq.comp reflect.continuous
  have hcr : HasCompactSupport (q ∘ reflect) := hc.comp_homeomorph reflect.toHomeomorph
  have hL := hi.locallyIntegrable hp
  have hU := hu.locallyIntegrable hp
  have hI := hL.integrable_smul_right_of_hasCompactSupport hq hc
  have hIR := hL.integrable_smul_right_of_hasCompactSupport hqr hcr
  simp only [smul_eq_mul, comp_apply] at hI hIR
  have hRI : Integrable (fun x => (halfSpace 2).indicator u (reflect x) * q x) := by
    simpa only [comp_def, reflect_reflect] using
      measurePreserving_reflect.integrable_comp_of_integrable hIR
  have hchange : (∫ x, (halfSpace 2).indicator u (reflect x) * q x) =
      ∫ x in halfSpace 2, u x * q (reflect x) := by
    rw [← integral_indicator_pair u (fun x => q (reflect x))]
    simpa only [comp_def, reflect_reflect] using
      measurePreserving_reflect.integral_comp reflect.toHomeomorph.measurableEmbedding
        (fun x => (halfSpace 2).indicator u x * q (reflect x))
  have hUH := hU.integrable_smul_right_of_hasCompactSupport hq hc
  have hUR := hU.integrable_smul_right_of_hasCompactSupport hqr hcr
  simp only [smul_eq_mul, comp_apply] at hUH hUR
  calc
    _ = (∫ x, (halfSpace 2).indicator u x * q x) +
        epsilon * ∫ x, (halfSpace 2).indicator u (reflect x) * q x := by
      rw [← integral_const_mul, ← integral_add hI (hRI.const_mul epsilon)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [m64BoundaryReflect]; ring
    _ = (∫ x in halfSpace 2, u x * q x) +
        epsilon * ∫ x in halfSpace 2, u x * q (reflect x) := by
      rw [integral_indicator_pair, hchange]
    _ = _ := by
      rw [← integral_const_mul, ← integral_add hUH (hUR.const_mul epsilon)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring





theorem m64BoundaryReflect_integral {u q : LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hq : Continuous q) (hc : HasCompactSupport q) (epsilon : ℝ) :
    (∫ x, m64BoundaryReflect epsilon u x * q x) =
      ∫ x in halfSpace 2, u x * (q x + epsilon * q (reflect x)) :=
  m64BoundaryReflect_integral_of_one_le (by norm_num) hu hq hc epsilon





theorem m64BoundaryReflect_integrable {u : LoopPlane → ℝ}
    (hu : IntegrableOn u (halfSpace 2)) (epsilon : ℝ) :
    Integrable (m64BoundaryReflect epsilon u) :=
  memLp_one_iff_integrable.mp
    (m64BoundaryReflect_memLp (memLp_one_iff_integrable.mpr hu) epsilon)

private theorem reflect_basis (i : Fin 2) :
    reflect (EuclideanSpace.single i 1) = coordinateSign i • EuclideanSpace.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [reflect]
  · simp [reflect, hj]




theorem m64Boundary_reflected_test_partial {phi : LoopPlane → ℝ}
    (hp : ContDiff ℝ ∞ phi) (epsilon : ℝ) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (fun q => phi q + epsilon * phi (reflect q)) p
      (EuclideanSpace.single i 1) =
        fderiv ℝ phi p (EuclideanSpace.single i 1) + epsilon * coordinateSign i *
          fderiv ℝ phi (reflect p) (EuclideanSpace.single i 1) := by
  have hd := hp.differentiable (by simp)
  have hr : HasFDerivAt (reflect (d := 2))
      reflect.toContinuousLinearEquiv.toContinuousLinearMap p :=
    reflect.toContinuousLinearEquiv.hasFDerivAt
  have hsum := (hd p).hasFDerivAt.add
    (((hd (reflect p)).hasFDerivAt.comp p hr).const_mul epsilon)
  change HasFDerivAt (fun q => phi q + epsilon * phi (reflect q)) _ p at hsum
  rw [hsum.fderiv]
  change _ + epsilon * fderiv ℝ phi (reflect p)
    (reflect (EuclideanSpace.single i 1)) = _
  rw [reflect_basis, map_smul, smul_eq_mul]
  change fderiv ℝ phi p (EuclideanSpace.single i 1) +
    epsilon * (coordinateSign i * fderiv ℝ phi (reflect p) (EuclideanSpace.single i 1)) = _
  ring






theorem m64HalfSpace_mixed_equation_reflect_of_one_le
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ} {R epsilon : ℝ} {p : ℝ≥0∞}
    (h_one : 1 ≤ p)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (halfSpace 2)))
    (hb : MemLp b p (volume.restrict (halfSpace 2)))
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ ball 0 R →
      (epsilon = -1 → ∀ p : LoopPlane, p 0 = 0 → phi p = 0) →
      (∫ p in halfSpace 2, ∑ i : Fin 2,
        F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
          ∫ p in halfSpace 2, b p * phi p) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ ball 0 R →
      (∫ p, ∑ i : Fin 2, m64BoundaryReflect (epsilon * coordinateSign i) (F i) p *
        fderiv ℝ phi p (EuclideanSpace.single i 1)) =
          ∫ p, m64BoundaryReflect epsilon b p * phi p := by
  intro phi hp hc hs
  let psi : LoopPlane → ℝ := fun p => phi p + epsilon * phi (reflect p)
  have hpsi : ContDiff ℝ ∞ psi := hp.add
    (contDiff_const.mul (hp.comp reflect.toContinuousLinearEquiv.contDiff))
  have hpc : HasCompactSupport psi :=
    hc.add (hc.comp_homeomorph reflect.toHomeomorph).mul_left
  have hps : tsupport psi ⊆ ball 0 R := by
    apply (tsupport_add _ _).trans
    apply union_subset hs
    apply tsupport_mul_subset_right.trans
    change tsupport (phi ∘ reflect.toHomeomorph) ⊆ ball 0 R
    rw [tsupport_comp_eq_preimage]
    intro p hpr
    have hh := hs hpr
    change dist (reflect p) 0 < R at hh
    simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh
  have hpface : epsilon = -1 → ∀ p : LoopPlane, p 0 = 0 → psi p = 0 := by
    intro he p hp0
    have hr : reflect p = p := by
      ext i
      by_cases hi : i = 0
      · subst i
        simp [hp0]
      · exact reflect_apply_ne p i hi
    simp [psi, he, hr]
  have hdcont (i : Fin 2) : Continuous
      (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) :=
    (hp.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcomp (i : Fin 2) := hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hIp (i : Fin 2) : Integrable (fun p =>
      m64BoundaryReflect (epsilon * coordinateSign i) (F i) p *
        fderiv ℝ phi p (EuclideanSpace.single i 1)) :=
    (m64BoundaryReflect_memLp (hF i) _).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) |>.integrable_smul_right_of_hasCompactSupport
        (hdcont i) (hdcomp i)
  have hIpsi (i : Fin 2) : IntegrableOn (fun p =>
      F i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) (halfSpace 2) :=
    (hF i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      |>.integrable_smul_right_of_hasCompactSupport
        ((hpsi.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hpc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  rw [integral_finsetSum _ (fun i _ => hIp i),
    m64BoundaryReflect_integral_of_one_le h_one hb hp.continuous hc epsilon]
  calc
    _ = ∑ i : Fin 2, ∫ p in halfSpace 2,
        F i p * fderiv ℝ psi p (EuclideanSpace.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [m64BoundaryReflect_integral (hF i) (hdcont i) (hdcomp i)]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => congrArg (fun z => F i p * z)
        (m64Boundary_reflected_test_partial hp epsilon p i).symm
    _ = ∫ p in halfSpace 2, ∑ i : Fin 2,
        F i p * fderiv ℝ psi p (EuclideanSpace.single i 1) :=
      (integral_finsetSum _ (fun i _ => hIpsi i)).symm
    _ = _ := heq psi hpsi hpc hps hpface




theorem m64HalfSpace_mixed_equation_reflect
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ} {R epsilon : ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (halfSpace 2)))
    (hb : MemLp b 2 (volume.restrict (halfSpace 2)))
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ ball 0 R →
      (epsilon = -1 → ∀ p : LoopPlane, p 0 = 0 → phi p = 0) →
      (∫ p in halfSpace 2, ∑ i : Fin 2,
        F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
          ∫ p in halfSpace 2, b p * phi p) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ ball 0 R →
      (∫ p, ∑ i : Fin 2, m64BoundaryReflect (epsilon * coordinateSign i) (F i) p *
        fderiv ℝ phi p (EuclideanSpace.single i 1)) =
          ∫ p, m64BoundaryReflect epsilon b p * phi p :=
  m64HalfSpace_mixed_equation_reflect_of_one_le (by norm_num) hF hb heq

end PoincareConjecture
