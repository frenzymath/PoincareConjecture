import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Annulus.SliceDifferential

/-!
# Smooth intrinsic currents for moving annuli

The time-space metric pairings are globally defined scalar functions of
the actual family differential. They are smooth without a single target
chart and without a positive-rank condition.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual scalar time-space pairing of a moving annulus. Source: Morgan--Tian (2007),
Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
noncomputable def m64MovingAnnulusCurrent (g : RiemannianMetric n M)
    (v : ℝ × LoopPlane → M) (i : Fin 2) (q : ℝ × LoopPlane) : ℝ :=
  g.inner (v q)
    (mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v q (1, 0))
    (mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v q
      (0, EuclideanSpace.basisFun (Fin 2) ℝ i))

/-- The actual time-space current is smooth wherever the family is smooth. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64MovingAnnulusCurrent_contDiffAt
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M} {q : ℝ × LoopPlane}
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v q) (i : Fin 2) :
    ContDiffAt ℝ ∞ (m64MovingAnnulusCurrent g v i) q := by
  have hpush (d : ℝ × LoopPlane) :
      ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) ((𝓡 n).prod (𝓡 n)) ∞
        (fun p => (⟨v p, mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v p d⟩ :
          TangentBundle (𝓡 n) M)) q := by
    have hd : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane)
        ((𝓘(ℝ, ℝ × LoopPlane)).prod 𝓘(ℝ, ℝ × LoopPlane)) ∞
        (fun p : ℝ × LoopPlane =>
          (⟨p, d⟩ : TangentBundle 𝓘(ℝ, ℝ × LoopPlane) (ℝ × LoopPlane))) q := by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := d)⟩
    exact (hv.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hd hv
  have h := ((g.contMDiff (v q)).comp q hv).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (hpush (1, 0)) (hpush (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
  exact contMDiffAt_iff_contDiffAt.mp (Bundle.contMDiffAt_totalSpace.mp h).2

omit [IsManifold (𝓡 n) ∞ M] in
/-- The actual time velocity is the time column of the joint differential. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64MovingAnnulus_time_velocity
    {v : ℝ × LoopPlane → M} {t : ℝ} {p : LoopPlane}
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v (t, p)) :
    curveVelocity (fun r => v (r, p)) t =
      mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v (t, p) (1, 0) := by
  have hline := hasFDerivAt_prodMk_left (𝕜 := ℝ) t p
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × LoopPlane)
      (fun r : ℝ => (r, p)) t := hline.differentiableAt.mdifferentiableAt
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × LoopPlane) (fun r : ℝ => (r, p)) t 1 =
      (1, 0) := by
    rw [mfderiv_eq_fderiv, hline.fderiv]
    rfl
  have hchain := mfderiv_comp_apply t hv hmd (1 : ℝ)
  rw [hd] at hchain
  exact hchain

omit [IsManifold (𝓡 n) ∞ M] in
/-- The source differential of a time slice is the actual joint spatial column, for any
source vector. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64MovingAnnulus_spatial_differential
    {v : ℝ × LoopPlane → M} {t : ℝ} {p : LoopPlane}
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v (t, p)) (d : LoopPlane) :
    mfderiv (𝓡 2) (𝓡 n) (fun z => v (t, z)) p d =
      mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v (t, p) (0, d) := by
  have hline := hasFDerivAt_prodMk_right (𝕜 := ℝ) t p
  have hmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × LoopPlane)
      (fun z : LoopPlane => (t, z)) p := hline.differentiableAt.mdifferentiableAt
  have hd : mfderiv (𝓡 2) 𝓘(ℝ, ℝ × LoopPlane) (fun z : LoopPlane => (t, z)) p d =
      (0, d) := by
    rw [mfderiv_eq_fderiv, hline.fderiv]
    rfl
  have hchain := mfderiv_comp_apply p hv hmd d
  rw [hd] at hchain
  exact hchain

/-- The scalar current is the genuine variation velocity paired with the actual spatial map
differential. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64MovingAnnulusCurrent_eq_pairing
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M} {t : ℝ} {p : LoopPlane}
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v (t, p)) (i : Fin 2) :
    m64MovingAnnulusCurrent g v i (t, p) =
      g.inner (v (t, p)) (curveVelocity (fun r => v (r, p)) t)
        (mfderiv (𝓡 2) (𝓡 n) (fun z => v (t, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  rw [m64MovingAnnulus_time_velocity hv, m64MovingAnnulus_spatial_differential hv]
  rfl

end PoincareMT
