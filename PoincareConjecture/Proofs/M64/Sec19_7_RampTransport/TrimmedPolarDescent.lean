import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarStandardCylinder










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)



def m64TrimmedCoverCoordinate (eps : ℝ) (z : Cover) : Plane :=
  annulusPoint (curvePeriod * z.2) (eps + (1 - 2 * eps) * (z.1 - 1))



def m64TrimmedAnnulusNeighborhood (eps : ℝ) : Set Plane :=
  {p | 0 < ‖p‖ ∧ eps + (1 - 2 * eps) * (‖p‖ - 1) ∈ Ioo (0 : ℝ) 1}




theorem m64TrimmedCoverCoordinate_contDiff (eps : ℝ) :
    ContDiff ℝ ∞ (m64TrimmedCoverCoordinate eps) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · simpa [m64TrimmedCoverCoordinate, annulusPoint] using
      (contDiff_const.mul contDiff_snd :
        ContDiff ℝ ∞ (fun z : Cover => curvePeriod * z.2))
  · simpa [m64TrimmedCoverCoordinate, annulusPoint] using
      (contDiff_const.add (contDiff_const.mul (contDiff_fst.sub contDiff_const)) :
        ContDiff ℝ ∞ (fun z : Cover => eps + (1 - 2 * eps) * (z.1 - 1)))

private theorem trimmedCoordinate_fderiv_injective {eps : ℝ}
    (heps : eps < 1 / 2) (z : Cover) :
    Function.Injective (fderiv ℝ (m64TrimmedCoverCoordinate eps) z) := by
  have ha : 1 - 2 * eps ≠ 0 := by linarith
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  let S : Plane → Cover := fun p => (1 + (p 1 - eps) / (1 - 2 * eps), p 0 / curvePeriod)
  have hS : ContDiff ℝ ∞ S := by
    exact (contDiff_const.add
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.sub contDiff_const).div_const
        (1 - 2 * eps))).prodMk
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.div_const curvePeriod)
  have hleft : S ∘ m64TrimmedCoverCoordinate eps = id := by
    funext w
    apply Prod.ext
    · change 1 + (eps + (1 - 2 * eps) * (w.1 - 1) - eps) / (1 - 2 * eps) = w.1
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ ha]
      ring
    · dsimp [S, m64TrimmedCoverCoordinate, annulusPoint]
      field_simp [hP]
  have hD := fderiv_comp z (hS.differentiable (by simp) _)
    ((m64TrimmedCoverCoordinate_contDiff eps).differentiable (by simp) z)
  intro u v huv
  have heq : fderiv ℝ (S ∘ m64TrimmedCoverCoordinate eps) z u =
      fderiv ℝ (S ∘ m64TrimmedCoverCoordinate eps) z v := by
    rw [hD]
    exact congrArg (fderiv ℝ S (m64TrimmedCoverCoordinate eps z)) huv
  simpa only [hleft, fderiv_id, ContinuousLinearMap.id_apply] using heq




theorem isOpen_m64TrimmedAnnulusNeighborhood (eps : ℝ) :
    IsOpen (m64TrimmedAnnulusNeighborhood eps) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_Ioo.preimage
      (continuous_const.add (continuous_const.mul (continuous_norm.sub continuous_const))))





theorem standardAnnulusDomain_subset_trimmedNeighborhood {eps : ℝ}
    (hpos : 0 < eps) (hsmall : eps < 1 / 2) :
    standardAnnulusDomain ⊆ m64TrimmedAnnulusNeighborhood eps := by
  intro p hp
  have ha : 0 < 1 - 2 * eps := by linarith
  have hlo := mul_nonneg ha.le (sub_nonneg.mpr hp.1)
  have hhi := mul_le_mul_of_nonneg_left (show ‖p‖ - 1 ≤ 1 by linarith [hp.2]) ha.le
  exact ⟨lt_of_lt_of_le zero_lt_one hp.1, by constructor <;> nlinarith⟩

private theorem cover_boundary (radius theta : ℝ) :
    scalarCoverMap (radius, theta / curvePeriod) = intrinsicAnnulusBoundary radius theta := by
  have hangle : 2 * Real.pi * (theta / curvePeriod) = theta := by
    unfold curvePeriod
    field_simp
  ext i
  fin_cases i <;> simp [scalarCoverMap, scalarCirclePoint, intrinsicAnnulusBoundary,
    EuclideanSpace.basisFun_apply, hangle]



theorem m64TrimmedDescent_standardCylinder
    {M : Type*} {f : Plane → M} {F : Plane → M} {eps : ℝ}
    (hdesc : ∀ z : Cover, 0 < z.1 →
      F (scalarCoverMap z) = f (m64TrimmedCoverCoordinate eps z))
    {p : Plane} (hp : 0 < p 1 + 1) :
    F (scalarStandardCylinderMap p) = f (annulusPoint (p 0) (eps + (1 - 2 * eps) * p 1)) := by
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  rw [scalarStandardCylinderMap, hdesc _ hp]
  congr 1
  simp [m64TrimmedCoverCoordinate, scalarCylinderCoordinate_apply, hP]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

private theorem trimmedDescent_smooth_immersedAt
    {f : Plane → M} {F : Plane → M} {eps : ℝ}
    (hsmall : eps < 1 / 2)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f Strip)
    (himm : ∀ p ∈ Strip, Function.Injective (mfderiv (𝓡 2) (𝓡 n) f p))
    (hdesc : ∀ z : Cover, 0 < z.1 →
      F (scalarCoverMap z) = f (m64TrimmedCoverCoordinate eps z))
    {z : Cover} (hz : 0 < z.1) (hstrip : m64TrimmedCoverCoordinate eps z ∈ Strip) :
    ContMDiffAt (𝓡 2) (𝓡 n) ∞ F (scalarCoverMap z) ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) F (scalarCoverMap z)) := by
  have hfo : ContMDiffAt (𝓡 2) (𝓡 n) ∞ f (m64TrimmedCoverCoordinate eps z) :=
    hf.contMDiffAt ((isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous).mem_nhds hstrip)
  have hT : ContMDiffAt 𝓘(ℝ, Cover) (𝓡 2) ∞ (m64TrimmedCoverCoordinate eps) z :=
    contMDiffAt_iff_contDiffAt.mpr (m64TrimmedCoverCoordinate_contDiff eps).contDiffAt
  have hcomp := hfo.comp z hT
  obtain ⟨q, hq, hqz, heq⟩ := scalarCoverDescent_local_germ hdesc hz
  have hqM : ContMDiffAt (𝓡 2) 𝓘(ℝ, Cover) ∞ q (scalarCoverMap z) :=
    contMDiffAt_iff_contDiffAt.mpr hq
  have hcompq : ContMDiffAt 𝓘(ℝ, Cover) (𝓡 n) ∞
      (f ∘ m64TrimmedCoverCoordinate eps) (q (scalarCoverMap z)) := hqz.symm ▸ hcomp
  have hF := (hcompq.comp _ hqM).congr_of_eventuallyEq heq
  refine ⟨hF, ?_⟩
  have hcover : F ∘ scalarCoverMap =ᶠ[𝓝 z] f ∘ m64TrimmedCoverCoordinate eps := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
    exact hdesc w hw
  have hpolar : MDifferentiableAt 𝓘(ℝ, Cover) (𝓡 2) scalarCoverMap z :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (scalarCoverMap_smooth.differentiable (by simp) z)
  have hD := hcover.mfderiv_eq (I := 𝓘(ℝ, Cover)) (I' := 𝓡 n)
  rw [mfderiv_comp z (hF.mdifferentiableAt (by simp)) hpolar,
    mfderiv_comp z (hfo.mdifferentiableAt (by simp)) (hT.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, mfderiv_eq_fderiv] at hD
  have hinj : Function.Injective
      ((mfderiv (𝓡 2) (𝓡 n) F (scalarCoverMap z)).comp (fderiv ℝ scalarCoverMap z)) := by
    rw [hD]
    exact (himm _ hstrip).comp (trimmedCoordinate_fderiv_injective hsmall z)
  obtain ⟨A, hA⟩ := scalarCoverMap_fderiv_invertible hz.ne'
  rw [← hA] at hinj
  intro u v huv
  obtain ⟨u, rfl⟩ := A.surjective u
  obtain ⟨v, rfl⟩ := A.surjective v
  exact congrArg A (hinj huv)





theorem m64_exists_trimmed_polar_descent
    {f : Plane → M}
    (hperiod : ∀ x s : ℝ, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f Strip)
    (himm : ∀ p ∈ Strip, Function.Injective (mfderiv (𝓡 2) (𝓡 n) f p))
    {eps : ℝ} (hpos : 0 < eps) (hsmall : eps < 1 / 2) :
    ∃ F : Plane → M,
      (∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f (m64TrimmedCoverCoordinate eps z)) ∧
      IsOpen (m64TrimmedAnnulusNeighborhood eps) ∧
      standardAnnulusDomain ⊆ m64TrimmedAnnulusNeighborhood eps ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ F (m64TrimmedAnnulusNeighborhood eps) ∧
      (∀ p ∈ m64TrimmedAnnulusNeighborhood eps,
        Function.Injective (mfderiv (𝓡 2) (𝓡 n) F p)) ∧
      (∀ theta : ℝ, F (intrinsicAnnulusBoundary 1 theta) = f (annulusPoint theta eps)) ∧
      ∀ theta : ℝ, F (intrinsicAnnulusBoundary 2 theta) = f (annulusPoint theta (1 - eps)) := by
  obtain ⟨F, hdesc⟩ := scalar_exists_periodic_cover_descent
    (f ∘ m64TrimmedCoverCoordinate eps) (by
      intro r t
      change f (annulusPoint (curvePeriod * (t + 1)) _) =
        f (annulusPoint (curvePeriod * t) _)
      rw [mul_add, mul_one, hperiod])
  have hregular {p : Plane} (hp : p ∈ m64TrimmedAnnulusNeighborhood eps) :
      ContMDiffAt (𝓡 2) (𝓡 n) ∞ F p ∧
        Function.Injective (mfderiv (𝓡 2) (𝓡 n) F p) := by
    obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjective_of_ne_zero (norm_pos_iff.mp hp.1)
    apply trimmedDescent_smooth_immersedAt hsmall hf himm hdesc hz
    change eps + (1 - 2 * eps) * (z.1 - 1) ∈ Ioo (0 : ℝ) 1
    simpa only [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos hz] using hp.2
  refine ⟨F, hdesc, isOpen_m64TrimmedAnnulusNeighborhood eps,
    standardAnnulusDomain_subset_trimmedNeighborhood hpos hsmall,
    (fun p hp => (hregular hp).1.contMDiffWithinAt), (fun p hp => (hregular hp).2), ?_, ?_⟩
  · intro theta
    have h := hdesc (1, theta / curvePeriod) (by norm_num)
    have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
    have hangle : curvePeriod * (theta / curvePeriod) = theta := by field_simp [hP]
    simpa only [cover_boundary, Function.comp_apply, m64TrimmedCoverCoordinate, Prod.fst, Prod.snd,
      sub_self, mul_zero, add_zero, hangle] using h
  · intro theta
    have h := hdesc (2, theta / curvePeriod) (by norm_num)
    have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
    have hangle : curvePeriod * (theta / curvePeriod) = theta := by field_simp [hP]
    have heps : eps + (1 - 2 * eps) = 1 - eps := by ring
    simpa only [cover_boundary, Function.comp_apply, m64TrimmedCoverCoordinate, Prod.fst, Prod.snd,
      show (2 : ℝ) - 1 = 1 by norm_num, mul_one, hangle, heps] using h

end PoincareConjecture
