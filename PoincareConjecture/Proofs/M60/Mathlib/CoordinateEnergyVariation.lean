import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Density









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Topology ContDiff

namespace PoincareConjecture.M60

open ConnectionVariation ConjugateVariation

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem hasDerivAt_affine_coordinate_energy
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {u V : P → E} (p d : P)
    (hB : DifferentiableAt ℝ B (u p))
    (hcompat : IsMetricCompatibleAt B Γ (u p))
    (hBsymm : ∀ a b, B (u p) a b = B (u p) b a)
    (hΓsymm : ∀ a b, Γ (u p) a b = Γ (u p) b a) :
    HasDerivAt
      (fun s : ℝ => (1 / 2 : ℝ) *
        B (u p + s • V p) (fderiv ℝ u p d + s • fderiv ℝ V p d)
          (fderiv ℝ u p d + s • fderiv ℝ V p d))
      (B (u p) (covDerivAlong Γ u V d p) (fderiv ℝ u p d)) 0 := by
  have hu : HasDerivAt (fun s : ℝ => u p + s • V p) (V p) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (V p)).const_add (u p)
  have hv : HasDerivAt
      (fun s : ℝ => fderiv ℝ u p d + s • fderiv ℝ V p d)
      (fderiv ℝ V p d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fderiv ℝ V p d)).const_add
      (fderiv ℝ u p d)
  have hB' : HasFDerivAt B (fderiv ℝ B (u p)) (u p + (0 : ℝ) • V p) := by
    simpa using hB.hasFDerivAt
  have hcoef := hB'.comp_hasDerivAt (l := B)
    (f := fun s : ℝ => u p + s • V p) 0 hu
  have h := ((hcoef.clm_apply hv).clm_apply hv).const_mul (1 / 2 : ℝ)
  convert! h using 1
  simp only [Function.comp_apply, zero_smul, add_zero, covDerivAlong_def, map_add,
    add_apply]
  rw [hcompat (V p) (fderiv ℝ u p d) (fderiv ℝ u p d)]
  rw [hΓsymm (V p), hBsymm (fderiv ℝ u p d),
    hBsymm (fderiv ℝ u p d)]
  ring



theorem hasDerivAt_coordinate_energy
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {u V : P → E} (p d : P)
    (hu : DifferentiableAt ℝ u p) (hV : DifferentiableAt ℝ V p)
    (hB : DifferentiableAt ℝ B (u p))
    (hcompat : IsMetricCompatibleAt B Γ (u p))
    (hBsymm : ∀ a b, B (u p) a b = B (u p) b a)
    (hΓsymm : ∀ a b, Γ (u p) a b = Γ (u p) b a) :
    HasDerivAt
      (fun s : ℝ => (1 / 2 : ℝ) * B (u p + s • V p)
        (fderiv ℝ (fun x => u x + s • V x) p d)
        (fderiv ℝ (fun x => u x + s • V x) p d))
      (B (u p) (covDerivAlong Γ u V d p) (fderiv ℝ u p d)) 0 := by
  apply (hasDerivAt_affine_coordinate_energy (V := V) p d
    hB hcompat hBsymm hΓsymm).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  have h := hu.hasFDerivAt.add (hV.hasFDerivAt.const_smul s)
  change HasFDerivAt (fun x => u x + s • V x) _ p at h
  dsimp only
  rw [h.fderiv]
  simp only [add_apply, smul_apply]

end PoincareConjecture.M60
