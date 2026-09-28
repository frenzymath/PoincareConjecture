import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TrimmedPolarDescent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarRoughAreaChange
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarRegularizedArea

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

def m64TrimmedStripMap (eps : ℝ) (p : Plane) : Plane :=
  annulusPoint (p 0) (eps + (1 - 2 * eps) * p 1)

def m64TrimmedCylinderFundamental (eps : ℝ) : Set Plane :=
  {p | p 1 ∈ Ioo eps (1 - eps) ∧ p 0 ∈ Ico (0 : ℝ) curvePeriod}

private theorem trimmedStrip_smooth (eps : ℝ) : ContDiff ℝ ∞ (m64TrimmedStripMap eps) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  · exact contDiff_const.add
      (contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)

private theorem trimmedStrip_injective {eps : ℝ} (hsmall : eps < 1 / 2) :
    Function.Injective (m64TrimmedStripMap eps) := by
  have ha : 1 - 2 * eps ≠ 0 := by linarith
  intro p q hpq
  have h0 := congrArg (fun x : Plane => x 0) hpq
  have h1 := congrArg (fun x : Plane => x 1) hpq
  change eps + (1 - 2 * eps) * p 1 = eps + (1 - 2 * eps) * q 1 at h1
  ext i
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ ha (add_left_cancel h1)

private theorem trimmedStrip_invertible {eps : ℝ} (hsmall : eps < 1 / 2) (p : Plane) :
    (fderiv ℝ (m64TrimmedStripMap eps) p).IsInvertible := by
  have ha : 1 - 2 * eps ≠ 0 := by linarith
  let S : Plane → Plane := fun q => annulusPoint (q 0) ((q 1 - eps) / (1 - 2 * eps))
  have hS : ContDiff ℝ ∞ S := by
    apply contDiff_euclidean.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
    · exact ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.sub contDiff_const).div_const
        (1 - 2 * eps)
  have hleft : S ∘ m64TrimmedStripMap eps = id := by
    funext q
    ext i
    fin_cases i
    · rfl
    · change (eps + (1 - 2 * eps) * q 1 - eps) / (1 - 2 * eps) = q 1
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ ha]
  let L := fderiv ℝ (m64TrimmedStripMap eps) p
  have hD := fderiv_comp p (hS.differentiable (by simp) _)
    ((trimmedStrip_smooth eps).differentiable (by simp) p)
  have hinj : Function.Injective L := by
    intro u v huv
    have heq : fderiv ℝ (S ∘ m64TrimmedStripMap eps) p u =
        fderiv ℝ (S ∘ m64TrimmedStripMap eps) p v := by
      rw [hD]
      exact congrArg (fderiv ℝ S (m64TrimmedStripMap eps p)) huv
    simpa only [hleft, fderiv_id, ContinuousLinearMap.id_apply] using heq
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hinj
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

private theorem trimmedStrip_image {eps : ℝ} (hsmall : eps < 1 / 2) :
    m64TrimmedStripMap eps '' scalarCylinderFundamental = m64TrimmedCylinderFundamental eps := by
  have ha : 0 < 1 - 2 * eps := by linarith
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    change (eps < eps + (1 - 2 * eps) * p 1 ∧
      eps + (1 - 2 * eps) * p 1 < 1 - eps) ∧ p 0 ∈ Ico (0 : ℝ) curvePeriod
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · exact lt_add_of_pos_right _ (mul_pos ha hp.1.1)
    · nlinarith [mul_lt_mul_of_pos_left hp.1.2 ha]
  · intro p hp
    let q := annulusPoint (p 0) ((p 1 - eps) / (1 - 2 * eps))
    have hq : q ∈ scalarCylinderFundamental := by
      change ((0 < (p 1 - eps) / (1 - 2 * eps)) ∧
        (p 1 - eps) / (1 - 2 * eps) < 1) ∧ p 0 ∈ Ico (0 : ℝ) curvePeriod
      exact ⟨⟨div_pos (sub_pos.mpr hp.1.1) ha,
        (div_lt_iff₀ ha).mpr (by nlinarith [hp.1.2])⟩, hp.2⟩
    refine ⟨q, hq, ?_⟩
    ext i
    fin_cases i
    · rfl
    · change eps + (1 - 2 * eps) * ((p 1 - eps) / (1 - 2 * eps)) = p 1
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha.ne', add_sub_cancel]

private theorem trimmedFundamental_subset {eps : ℝ} (hpos : 0 < eps) :
    m64TrimmedCylinderFundamental eps ⊆ m64AnnulusDomain := by
  intro p hp
  exact ⟨hp.2.1, hp.2.2.le, (hpos.trans hp.1.1).le, by linarith [hp.1.2]⟩

private theorem openAnnulus_ae_eq_standard :
    scalarAnnulus =ᵐ[volume] standardAnnulusDomain := by
  simpa only [scalarAnnulusDefining_nonneg, standardAnnulusDomain] using scalarAnnulus_ae_eq_closed

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem trimmedDescent_density
    (g : RiemannianMetric n M) {f : Plane → M} {F : Plane → M} {eps : ℝ}
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f (m64TrimmedCoverCoordinate eps z))
    {p : Plane} (hp : p ∈ Strip) :
    |(fderiv ℝ scalarStandardCylinderMap p).det| *
      m60AreaDensity g F (scalarStandardCylinderMap p) =
        m60AreaDensity g (f ∘ m64TrimmedStripMap eps) p := by
  rw [← scalarAreaDensity_comp_localDiffeomorph g F
    (scalarStandardCylinderMap_smooth.contDiffAt.of_le (by simp))
    (scalarStandardCylinderMap_invertible hp)]
  apply m60AreaDensity_congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous).mem_nhds hp] with q hq
  have hq0 : 0 < q 1 := hq.1
  exact m64TrimmedDescent_standardCylinder hdesc (by linarith)

theorem m64TrimmedPolarDescent_area
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    {F : Plane → M} {eps : ℝ} (hpos : 0 < eps) (hsmall : eps < 1 / 2)
    (hdesc : ∀ z : Cover, 0 < z.1 →
      F (scalarCoverMap z) = A.map (m64TrimmedCoverCoordinate eps z)) :
    IntegrableOn (m60AreaDensity g F) standardAnnulusDomain ∧
      (∫ p in standardAnnulusDomain, m60AreaDensity g F p) =
        ∫ p in m64TrimmedCylinderFundamental eps, m60AreaDensity g A.map p ∧
      (∫ p in standardAnnulusDomain, m60AreaDensity g F p) ≤ A.area := by
  have hTD (p : Plane) : HasFDerivAt (m64TrimmedStripMap eps)
      (fderiv ℝ (m64TrimmedStripMap eps) p) p :=
    ((trimmedStrip_smooth eps).differentiable (by simp) p).hasFDerivAt
  have hTchange := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable (fun p _ => (hTD p).hasFDerivWithinAt)
    (trimmedStrip_injective hsmall).injOn (m60AreaDensity g A.map)
  rw [trimmedStrip_image hsmall] at hTchange
  have hAI : IntegrableOn (m60AreaDensity g A.map) (m64TrimmedCylinderFundamental eps) :=
    A.area_integrable.mono_set (trimmedFundamental_subset hpos)
  have hCI : IntegrableOn (m60AreaDensity g (A.map ∘ m64TrimmedStripMap eps))
      scalarCylinderFundamental := by
    apply (hTchange.mp hAI).congr_fun _ scalarCylinderFundamental_measurable
    intro p _
    simpa only [smul_eq_mul] using (scalarAreaDensity_comp_localDiffeomorph g A.map
      ((trimmedStrip_smooth eps).contDiffAt.of_le (by simp))
      (trimmedStrip_invertible hsmall p)).symm
  have hCD (p : Plane) : HasFDerivAt scalarStandardCylinderMap
      (fderiv ℝ scalarStandardCylinderMap p) p :=
    (scalarStandardCylinderMap_smooth.differentiable (by simp) p).hasFDerivAt
  have hCchange := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable (fun p _ => (hCD p).hasFDerivWithinAt)
    scalarStandardCylinderMap_injOn (m60AreaDensity g F)
  rw [scalarStandardCylinderMap_image] at hCchange
  have hFI : IntegrableOn (m60AreaDensity g F) scalarAnnulus := by
    apply hCchange.mpr
    apply hCI.congr_fun _ scalarCylinderFundamental_measurable
    intro p hp
    simpa only [smul_eq_mul] using (trimmedDescent_density g hdesc hp.1).symm
  have hCint := integral_image_eq_integral_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable (fun p _ => (hCD p).hasFDerivWithinAt)
    scalarStandardCylinderMap_injOn (m60AreaDensity g F)
  rw [scalarStandardCylinderMap_image] at hCint
  have hTint := integral_image_eq_integral_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable (fun p _ => (hTD p).hasFDerivWithinAt)
    (trimmedStrip_injective hsmall).injOn (m60AreaDensity g A.map)
  rw [trimmedStrip_image hsmall] at hTint
  have harea : (∫ p in scalarAnnulus, m60AreaDensity g F p) =
      ∫ p in m64TrimmedCylinderFundamental eps, m60AreaDensity g A.map p := by
    calc
      _ = ∫ p in scalarCylinderFundamental,
          |(fderiv ℝ scalarStandardCylinderMap p).det| *
            m60AreaDensity g F (scalarStandardCylinderMap p) := by
        simpa only [smul_eq_mul] using hCint
      _ = ∫ p in scalarCylinderFundamental,
          m60AreaDensity g (A.map ∘ m64TrimmedStripMap eps) p :=
        setIntegral_congr_fun scalarCylinderFundamental_measurable
          (fun _ hp => trimmedDescent_density g hdesc hp.1)
      _ = ∫ p in scalarCylinderFundamental,
          |(fderiv ℝ (m64TrimmedStripMap eps) p).det| *
            m60AreaDensity g A.map (m64TrimmedStripMap eps p) :=
        setIntegral_congr_fun scalarCylinderFundamental_measurable (fun p _ =>
          scalarAreaDensity_comp_localDiffeomorph g A.map
            ((trimmedStrip_smooth eps).contDiffAt.of_le (by simp))
            (trimmedStrip_invertible hsmall p))
      _ = _ := by simpa only [smul_eq_mul] using hTint.symm
  have hclosed : (∫ p in standardAnnulusDomain, m60AreaDensity g F p) =
      ∫ p in m64TrimmedCylinderFundamental eps, m60AreaDensity g A.map p :=
    (setIntegral_congr_set openAnnulus_ae_eq_standard).symm.trans harea
  refine ⟨(integrableOn_congr_set_ae openAnnulus_ae_eq_standard).mp hFI, hclosed, ?_⟩
  rw [hclosed]
  exact setIntegral_mono_set A.area_integrable
    (Eventually.of_forall (m60AreaDensity_nonneg g A.map))
    (Eventually.of_forall (trimmedFundamental_subset hpos))

theorem m64TrimmedPolarDescent_intrinsic_area_le
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    {F : Plane → M} {eps : ℝ} (hpos : 0 < eps) (hsmall : eps < 1 / 2)
    (hdesc : ∀ z : Cover, 0 < z.1 →
      F (scalarCoverMap z) = A.map (m64TrimmedCoverCoordinate eps z))
    (h : RiemannianMetric 2 Plane)
    (hmetric : ∀ p ∈ standardAnnulusDomain, ∀ u v : Plane,
      h.inner p u v = g.inner (F p) (mfderiv (𝓡 2) (𝓡 n) F p u)
        (mfderiv (𝓡 2) (𝓡 n) F p v)) :
    intrinsicAnnulusArea h ≤ A.area := by
  have hS : MeasurableSet standardAnnulusDomain :=
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet
  have heq : intrinsicAnnulusArea h = ∫ p in standardAnnulusDomain, m60AreaDensity g F p := by
    apply setIntegral_congr_fun hS
    intro p hp
    have hgram : (fun i j : Fin 2 => h.inner p (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j)) = m60AreaGram g F p := by
      ext i j
      exact hmetric p hp _ _
    change Real.sqrt (max 0 (Matrix.det _)) = Real.sqrt (max 0 (Matrix.det _))
    rw [hgram]
  exact heq.trans_le (m64TrimmedPolarDescent_area A hpos hsmall hdesc).2.2

end PoincareConjecture
