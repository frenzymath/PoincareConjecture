import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.RadialGeometry
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Periodic.GreenIdentity

/-!
# Actual Green flux of the prescribed lower boundary curve

The constant-radial extension of a C1 curve has its classical columns.
Its translated rectangle Green identity supplies the positive interface
flux which cancels the original weak annulus's negative boundary flux.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "v" => m64AnnulusRadialTranslation

/-- Subtracting the radial translation reduces the actual radial coordinate by one. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
theorem m64AnnulusPoint_sub_radialTranslation (x s : ℝ) :
    annulusPoint x s - v = annulusPoint x (s - 1) := by
  ext i
  fin_cases i <;> simp [m64AnnulusRadialTranslation, annulusPoint]

/-- Differentiate an actual translated C1 map without changing its derivative direction.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
theorem m64FDeriv_sub_translation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : LoopPlane → E} (hf : ContDiff ℝ 1 f) (a p w : LoopPlane) :
    fderiv ℝ (fun q => f (q - a)) p w = fderiv ℝ f (p - a) w := by
  have ht := (hasFDerivAt_id (𝕜 := ℝ) p).sub_const a
  have hd := ((hf.differentiable (by norm_num) (p - a)).hasFDerivAt.comp p ht).fderiv
  have h := congrArg (fun L : LoopPlane →L[ℝ] E => L w) hd
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

/-- A test supported inside the reflected strip vanishes on its four outer edges. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
theorem m64LowerTest_boundary_zero {phi : LoopPlane → ℝ} (hs : tsupport phi ⊆ O) :
    (∀ x : ℝ, phi (annulusPoint x 1) = 0) ∧
    (∀ x : ℝ, phi (annulusPoint x (-1)) = 0) ∧
    (∀ s : ℝ, phi (annulusPoint 0 s) = 0) ∧
    (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) := by
  have hz {p : LoopPlane} (hp : p ∉ O) : phi p = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hp (hs h)
  refine ⟨fun x => hz ?_, fun x => hz ?_, fun s => hz ?_, fun s => hz ?_⟩ <;>
    simp [m64AnnulusLowerDomain, annulusPoint]

/-- The constant-radial extension of a C1 curve is C1 on the source plane. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
theorem m64BoundaryCurvePlane_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ → E} (hc : ContDiff ℝ 1 c) : ContDiff ℝ 1 (fun p : LoopPlane => c (p 0)) :=
  hc.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff

/-- The actual lower-strip curve extension supplies the positive interface Green flux. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
theorem m64Annulus_lower_boundaryCurve_green
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {c : ℝ → E} (hc : ContDiff ℝ 1 c)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in S, phi (p - v) •
      fderiv ℝ (fun q : LoopPlane => c (q 0)) p (EuclideanSpace.single i 1)) +
      (∫ p in S, fderiv ℝ phi (p - v) (EuclideanSpace.single i 1) • c (p 0)) =
      if i = 1 then ∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) • c x else 0 := by
  let C : LoopPlane → E := fun p => c (p 0)
  let psi : LoopPlane → ℝ := fun p => phi (p - v)
  have hC : ContDiff ℝ 1 C := m64BoundaryCurvePlane_contDiff hc
  have hpsi : ContDiff ℝ 1 psi := hp.comp (contDiff_id.sub contDiff_const)
  have hder (p : LoopPlane) (j : Fin 2) :
      fderiv ℝ psi p (EuclideanSpace.single j 1) =
        fderiv ℝ phi (p - v) (EuclideanSpace.single j 1) := m64FDeriv_sub_translation hp v p _
  obtain ⟨-, hbottom, hleft, hright⟩ := m64LowerTest_boundary_zero hs
  fin_cases i
  · have h := m64Annulus_horizontal_green_identity hC hpsi
    simp_rw [hder] at h
    rw [show (fun q : LoopPlane => c (q 0)) = C from rfl]
    change (∫ p in S, psi p • fderiv ℝ C p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi (p - v) (EuclideanSpace.single (0 : Fin 2) 1) • C p) = 0
    rw [h]
    apply integral_eq_zero_of_ae
    filter_upwards [] with s
    simp only [psi, m64AnnulusPoint_sub_radialTranslation, hleft, hright,
      zero_smul, sub_self, Pi.zero_apply]
  · have h := m64Annulus_vertical_green_identity hC hpsi
    simp_rw [hder] at h
    rw [show (fun q : LoopPlane => c (q 0)) = C from rfl]
    change (∫ p in S, psi p • fderiv ℝ C p (EuclideanSpace.single (1 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi (p - v) (EuclideanSpace.single (1 : Fin 2) 1) • C p) = _
    rw [h]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [psi]
    rw [m64AnnulusPoint_sub_radialTranslation, m64AnnulusPoint_sub_radialTranslation]
    change phi (annulusPoint x (1 - 1)) • c x - phi (annulusPoint x (0 - 1)) • c x = _
    simp only [sub_self, zero_sub, hbottom, zero_smul, sub_zero]

end PoincareMT
