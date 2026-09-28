import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateCoefficients
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 800000 in

theorem m64WeightedChart_scalar_equation
    (g : RiemannianMetric n M) (b : M) (modulus : ℝ)
    {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall a R))
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hvar : ∀ phi : LoopPlane → E, ContDiff ℝ ∞ phi →
      tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)) →
      (∀ p : LoopPlane, p 1 ≤ 0 → phi p = 0) →
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      (∫ p in ball a (R / 2),
        (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
            2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
          modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
            2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2) = 0)
    (j : Fin n) {psi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ ball a ((R / 4) * Real.exp (-1)) ∩ {p : LoopPlane | 0 < p 1}) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    (∫ p in ball a (R / 2), ∑ i : Fin 2,
      ((if i = 0 then modulus else modulus⁻¹) * G (u p) (W i p)
        (EuclideanSpace.single j 1)) * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
      ∫ p in ball a (R / 2),
        (-(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (W 0 p) (W 0 p) +
          modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (W 1 p) (W 1 p)) / 2) *
          psi p := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let flux := fun (i : Fin 2) (p : LoopPlane) =>
    (if i = 0 then modulus else modulus⁻¹) * G (u p) (W i p) (EuclideanSpace.single j 1)
  let source := fun p =>
    -(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (W 0 p) (W 0 p) +
      modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (W 1 p) (W 1 p)) / 2
  let phi := fun p : LoopPlane => psi p • EuclideanSpace.single j (1 : ℝ)
  have hphi : ContDiff ℝ ∞ phi := hp.smul contDiff_const
  have hphis : tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)) :=
    (tsupport_smul_subset_left _ _).trans (hs.trans inter_subset_left)
  have hphiz (p : LoopPlane) (hz : p 1 ≤ 0) : phi p = 0 := by
    have hpsiz : psi p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hm => (not_lt_of_ge hz) (hs hm).2)
    simp only [phi, hpsiz, zero_smul]
  have hd (p : LoopPlane) (i : Fin 2) :
      fderiv ℝ phi p (EuclideanSpace.single i 1) =
        fderiv ℝ psi p (EuclideanSpace.single i 1) • EuclideanSpace.single j (1 : ℝ) := by
    rw [((hp.differentiable (by simp) p).hasFDerivAt.smul_const
      (EuclideanSpace.single j (1 : ℝ))).fderiv]
    rfl
  have hhalf : ball a (R / 2) ⊆ ball a R := ball_subset_ball (half_le_self hR.le)
  obtain ⟨hF, hB⟩ := m64WeightedChart_flux_source_memLp g b modulus hu huT hW
  have hFI (i : Fin 2) : MemLp (flux i) 2 (volume.restrict (ball a (R / 2))) :=
    (hF j i).mono_measure (Measure.restrict_mono hhalf le_rfl)
  have hBI : IntegrableOn source (ball a (R / 2)) := (hB j).mono_set hhalf
  have hDI (i : Fin 2) : MemLp
      (fun p => fderiv ℝ psi p (EuclideanSpace.single i 1)) 2
      (volume.restrict (ball a (R / 2))) :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const
      ).memLp_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)
      ).mono_measure Measure.restrict_le_self
  have hLI : IntegrableOn (fun p => ∑ i : Fin 2,
      flux i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) (ball a (R / 2)) :=
    integrable_finsetSum _ fun i _ => (hFI i).integrable_mul (hDI i)
  have hRI : IntegrableOn (fun p => source p * psi p) (ball a (R / 2)) := by
    have hpsi : MemLp psi ⊤ (volume.restrict (ball a (R / 2))) :=
      (hp.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
    exact memLp_one_iff_integrable.mp
      (hpsi.mul' (memLp_one_iff_integrable.mpr hBI))
  have heq := hvar phi hphi hphis hphiz
  have hrate : (fun p : LoopPlane =>
      (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
          2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
        modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
          2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2) =
      (fun p =>
        (∑ i : Fin 2, flux i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) -
          source p * psi p) := by
    funext p
    simp only [hd, phi, map_smul, smul_apply, smul_eq_mul, Fin.sum_univ_two, flux,
      source, one_ne_zero, ↓reduceIte]
    ring
  dsimp only at heq
  rw [hrate, integral_sub hLI hRI] at heq
  exact sub_eq_zero.mp heq

end PoincareConjecture
