import PoincareConjecture.Proofs.M08.SquareVariationConstruction
import PoincareConjecture.Proofs.M08.VariationAcceleration
import PoincareConjecture.Proofs.M08.Endpoints

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
  {p : BackwardTimePath F T τ₁ τ₂}

def supportedChartShift (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ) (z : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  variationChart V x z + (z.2 * c) • η z.1

def supportedChartDomain (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ) : Set (ℝ × ℝ) :=
  (variationChartDomain V x ∩ supportedChartShift V x η c ⁻¹' (extChartAt (𝓡 n) x).target) ∪
    (V.squareDomain ∩ Prod.fst ⁻¹' (tsupport η)ᶜ)

def supportedChartFamily (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ) (z : ℝ × ℝ) : M := by
  classical
  exact if z.1 ∈ tsupport η then
    (extChartAt (𝓡 n) x).symm (supportedChartShift V x η c z)
  else V.squareFamily z.1 z.2

theorem supportedChartShift_contDiffOn (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η) (c : ℝ) :
    ContDiffOn ℝ ∞ (supportedChartShift V x η c) (variationChartDomain V x) :=
  (variationChart_contDiffOn V x).add
    (((contDiff_snd.mul contDiff_const).smul (hη.comp contDiff_fst)).contDiffOn)

theorem supportedChartDomain_open (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η) (c : ℝ) :
    IsOpen (supportedChartDomain V x η c) :=
  ((supportedChartShift_contDiffOn V x η hη c).continuousOn.isOpen_inter_preimage
    (variationChartDomain_open V x) (isOpen_extChartAt_target (I := 𝓡 n) x)).union
    (V.square_open.inter ((isClosed_tsupport η).isOpen_compl.preimage continuous_fst))

theorem supportedChartFamily_eq_of_not_support (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ) {z : ℝ × ℝ}
    (hz : z.1 ∉ tsupport η) :
    supportedChartFamily V x η c z = V.squareFamily z.1 z.2 := by
  simp only [supportedChartFamily, if_neg hz]

theorem supportedChartFamily_eq_chart (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ) {z : ℝ × ℝ}
    (hz : V.squareFamily z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    supportedChartFamily V x η c z =
      (extChartAt (𝓡 n) x).symm (supportedChartShift V x η c z) := by
  classical
  by_cases hs : z.1 ∈ tsupport η
  · simp only [supportedChartFamily, if_pos hs]
  · rw [supportedChartFamily_eq_of_not_support V x η c hs]
    have hηzero : η z.1 = 0 := image_eq_zero_of_notMem_tsupport hs
    simp only [supportedChartShift, hηzero, smul_zero, add_zero, variationChart]
    exact ((extChartAt (𝓡 n) x).left_inv
      (by simpa only [extChartAt_source] using hz)).symm

theorem supportedChartFamily_contMDiffOn (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η) (c : ℝ) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (supportedChartFamily V x η c) (supportedChartDomain V x η c) := by
  let U := variationChartDomain V x ∩
    supportedChartShift V x η c ⁻¹' (extChartAt (𝓡 n) x).target
  let W := V.squareDomain ∩ Prod.fst ⁻¹' (tsupport η)ᶜ
  have hU : IsOpen U := (supportedChartShift_contDiffOn V x η hη c).continuousOn.isOpen_inter_preimage
    (variationChartDomain_open V x) (isOpen_extChartAt_target (I := 𝓡 n) x)
  have hW : IsOpen W := V.square_open.inter
    ((isClosed_tsupport η).isOpen_compl.preimage continuous_fst)
  have hshift : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (supportedChartShift V x η c) U := by
    have h := ((supportedChartShift_contDiffOn V x η hη c).mono
      (show U ⊆ variationChartDomain V x from inter_subset_left)).contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hchart := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x).comp
    hshift (fun z hz ↦ hz.2)
  have hleft : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (supportedChartFamily V x η c) U := by
    apply hchart.congr
    intro z hz
    exact supportedChartFamily_eq_chart V x η c hz.1.2
  have hright : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (supportedChartFamily V x η c) W := by
    apply (V.square_smooth.mono inter_subset_left).congr
    intro z hz
    exact supportedChartFamily_eq_of_not_support V x η c hz.2
  exact hleft.union_of_isOpen hright hU hW

theorem supportedChartDomain_zero (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    sqrtParameterInterval τ₁ τ₂ ×ˢ {(0 : ℝ)} ⊆ supportedChartDomain V x η c := by
  rintro ⟨s, v⟩ ⟨hs, hv⟩
  obtain rfl := mem_singleton_iff.mp hv
  have hdom : (s, (0 : ℝ)) ∈ V.squareDomain :=
    V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  by_cases hsupport : s ∈ tsupport η
  · left
    refine ⟨⟨hdom, hsrc s hs hsupport⟩, ?_⟩
    simp only [mem_preimage, supportedChartShift, zero_mul, zero_smul, add_zero, variationChart]
    exact (extChartAt (𝓡 n) x).map_source
      (by simpa only [extChartAt_source, LVariation.baseSquareCurve] using hsrc s hs hsupport)
  · exact Or.inr ⟨hdom, hsupport⟩

theorem supportedChartFamily_at_zero (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    supportedChartFamily V x η c (s, 0) = V.baseSquareCurve s := by
  by_cases hsupport : s ∈ tsupport η
  · rw [supportedChartFamily_eq_chart V x η c (z := (s, 0)) (hsrc s hs hsupport)]
    simp only [supportedChartShift, zero_mul, zero_smul, add_zero, variationChart]
    exact (extChartAt (𝓡 n) x).left_inv
      (by simpa only [extChartAt_source, LVariation.baseSquareCurve] using hsrc s hs hsupport)
  · exact supportedChartFamily_eq_of_not_support V x η c hsupport

theorem supportedChartFamily_eq_of_zero (V : LVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ supportedChartDomain V x η c) (hzero : η z.1 = 0) :
    supportedChartFamily V x η c z = V.squareFamily z.1 z.2 := by
  rcases hz with hz | hz
  · rw [supportedChartFamily_eq_chart V x η c hz.1.2]
    simp only [supportedChartShift, hzero, smul_zero, add_zero, variationChart]
    exact (extChartAt (𝓡 n) x).left_inv
      (by simpa only [extChartAt_source] using
        (show V.squareFamily z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source from
          hz.1.2))
  · exact supportedChartFamily_eq_of_not_support V x η c hz.2

theorem exists_supportedChartVariation (hM04 : RicciFlowCurvatureTheory.{u})
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) (x : M)
    (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η) (c : ℝ)
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.toLVariation.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hleft : η (Real.sqrt τ₁) = 0) (hright : η (Real.sqrt τ₂) = 0) :
    ∃ W : FixedEndpointLVariation F T τ₁ τ₂ p,
      W.radius ≤ V.radius ∧
      (∀ s v, W.squareFamily s v = supportedChartFamily V.toLVariation x η c (s, v)) ∧
      EqOn W.toLVariation.baseSquareCurve V.toLVariation.baseSquareCurve
        (sqrtParameterInterval τ₁ τ₂) := by
  let H := supportedChartFamily V.toLVariation x η c
  let Ω := supportedChartDomain V.toLVariation x η c
  have hΩ := supportedChartDomain_open V.toLVariation x η hη c
  have hH := supportedChartFamily_contMDiffOn V.toLVariation x η hη c
  obtain ⟨r, hr, hrV, hCr⟩ := exists_squareTube_radius isCompact_Icc hΩ
    (supportedChartDomain_zero V.toLVariation x η c hsrc) V.radius_pos
  have hzero (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
      H (s, 0) = p.curve (s ^ 2) :=
    (supportedChartFamily_at_zero V.toLVariation x η c hsrc hs).trans
      ((V.square_agrees s hs 0 ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩).trans
        (V.at_zero (s ^ 2)))
  have hparameter (v : ℝ) (hv : v ∈ Ioo (-r) r) : v ∈ V.toLVariation.parameterDomain :=
    ⟨(neg_le_neg hrV).trans_lt hv.1, hv.2.trans_le hrV⟩
  have hL (v : ℝ) (hv : v ∈ Ioo (-r) r) : H (Real.sqrt τ₁, v) = p.curve τ₁ := by
    rw [show H (Real.sqrt τ₁, v) = V.squareFamily (Real.sqrt τ₁) v from
      supportedChartFamily_eq_of_zero V.toLVariation x η c
        (hCr ⟨⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩, hv⟩) hleft]
    exact squareFamily_left_eq V.toInitialFixedLVariation (hparameter v hv)
  have hR (v : ℝ) (hv : v ∈ Ioo (-r) r) : H (Real.sqrt τ₂, v) = p.curve τ₂ := by
    rw [show H (Real.sqrt τ₂, v) = V.squareFamily (Real.sqrt τ₂) v from
      supportedChartFamily_eq_of_zero V.toLVariation x η c
        (hCr ⟨⟨Real.sqrt_le_sqrt p.ordered.le, le_rfl⟩, hv⟩) hright]
    exact squareFamily_right_eq V (hparameter v hv)
  let W := fixedVariationOfSquare hM04 p H Ω hΩ r hr hCr hH hzero hL hR
  exact ⟨W, hrV, fun _ _ ↦ rfl, fun s hs ↦
    supportedChartFamily_at_zero V.toLVariation x η c hsrc hs⟩

end PoincareConjecture.M08

