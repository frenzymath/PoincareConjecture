import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingScalars
import PoincareConjecture.Proofs.M62.Lemma0_2_NormalizedFields











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (d : ℝ → ℝ → M)



theorem unitTangent_mdifferentiable (hd : M62ShrinkingCurve F d)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M)) := by
  intro x
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ x, ht⟩
  have hj := ((M62.unitTangent_joint_contMDiff F d hd).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  exact hj.comp x hs



theorem smooth_curvatureVector_comp (hd : M62ShrinkingCurve F d)
    {phi : ℝ → ℝ} (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    m62CurvatureVector F (fun y s => d (phi y) s) t x =
      m62CurvatureVector F d t (phi x) := by
  exact curvatureVector_comp F d
    ((hd.spatial_regular t (Ioo_subset_Icc_self ht)).mdifferentiable (by norm_num))
    hphi hpos (unitTangent_mdifferentiable F d hd ht (phi x))



theorem curvatureJet_joint_contMDiff [T2Space M] (hd : M62ShrinkingCurve F d)
    (i : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ =>
        (⟨d z.1 z.2, m63CurvatureJet F d i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
  induction i with
  | zero => exact M62.curvature_joint_contMDiff F d hd
  | succ i ih =>
    exact M62.spatialDerivative_joint_contMDiff F d hd
      (fun z => m63CurvatureJet F d i z.2 z.1) ih



theorem curvatureJet_mdifferentiable [T2Space M] (hd : M62ShrinkingCurve F d)
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) :
    MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, m63CurvatureJet F d i t y⟩ : TangentBundle (𝓡 n) M)) := by
  intro x
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ x, ht⟩
  have hj := ((curvatureJet_joint_contMDiff F d hd i).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  exact hj.comp x hs



theorem smooth_curvatureJet_comp [T2Space M] (hd : M62ShrinkingCurve F d)
    {phi : ℝ → ℝ} (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) (x : ℝ) :
    m63CurvatureJet F (fun y s => d (phi y) s) i t x =
      m63CurvatureJet F d i t (phi x) := by
  exact curvatureJet_comp F d
    ((hd.spatial_regular t (Ioo_subset_Icc_self ht)).mdifferentiable (by norm_num))
    hphi hpos (fun y => unitTangent_mdifferentiable F d hd ht (phi y))
    (fun j y => curvatureJet_mdifferentiable F d hd ht j (phi y)) i x



theorem smooth_curvatureJetSquared_comp [T2Space M] (hd : M62ShrinkingCurve F d)
    {phi : ℝ → ℝ} (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) (x : ℝ) :
    m63CurvatureJetSquared F (fun y s => d (phi y) s) i t x =
      m63CurvatureJetSquared F d i t (phi x) := by
  unfold m63CurvatureJetSquared
  rw [smooth_curvatureJet_comp F d hd hphi hpos ht i x]

section CircleProduct

variable {F' : RicciFlow n M (Icc a b)} {circumference : ℝ}
  (P : M62.CircleProductData F' circumference) (c : ℝ → ℝ → P.charts.Point)



theorem smooth_rampRatio_comp (hc : M62ShrinkingCurve P.flow c)
    {phi : ℝ → ℝ} (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Ioo a b) (epsilon x : ℝ) :
    m63RampRatio P (fun y s => c (phi y) s) epsilon t x =
      m63RampRatio P c epsilon t (phi x) := by
  let := P.charts.chartedSpace
  exact rampRatio_comp P c
    ((hc.spatial_regular t (Ioo_subset_Icc_self ht)).mdifferentiable (by norm_num))
    hphi hpos (unitTangent_mdifferentiable P.flow c hc ht (phi x)) epsilon

end CircleProduct

end PoincareConjecture.M63
