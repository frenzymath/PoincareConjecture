import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityInverseChart
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem m64WeakCoordinates_scalar_memW1p {n : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContinuousOn u (closedBall a R))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hrange : MapsTo u (closedBall a R) K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiffOn ℝ 1 F O) :
    MemW1p 2 (F ∘ u) (ball a r) := by
  let V := fun i p => fderiv ℝ F (u p) (W i p)
  have hmap : MapsTo u (closedBall a R) O := fun _ hp => hKO (hrange hp)
  have hFu : ContinuousOn (F ∘ u) (closedBall a R) := hF.continuousOn.comp hu hmap
  have hDFu : ContinuousOn (fun p => fderiv ℝ F (u p)) (closedBall a R) :=
    (hF.continuousOn_fderiv_of_isOpen hO (by simp)).comp hu hmap
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hDFu
  have hVfull (i : Fin 2) : MemLp (V i) 2 (volume.restrict (ball a R)) := by
    have hmeas : AEStronglyMeasurable (fun p => fderiv ℝ F (u p))
        (volume.restrict (ball a R)) :=
      (hDFu.mono ball_subset_closedBall).aestronglyMeasurable isOpen_ball.measurableSet
    have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hmeas.prodMk (hW i).aestronglyMeasurable)
    apply ((hW i).norm.const_mul C).mono' hm
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hp
    exact (fderiv ℝ F (u p)).le_opNorm (W i p) |>.trans
      (mul_le_mul_of_nonneg_right (hC p (ball_subset_closedBall hp)) (norm_nonneg _))
  have hsub : ball a r ⊆ ball a R := ball_subset_ball hrR.le
  refine ⟨(m64MemLp_on_ball_of_continuous_closedBall hFu 2).mono_measure
    (Measure.restrict_mono hsub le_rfl), ?_⟩
  intro i
  exact ⟨V i, (hVfull i).mono_measure (Measure.restrict_mono hsub le_rfl),
    M60.suWeakPartial_comp_on_compact hr hrR
      (m64MemLp_on_ball_of_continuous_closedBall hu 4) hW hw hO hK hKO hrange hF i⟩

theorem m64Coordinate_compact_phase_change {n : ℕ}
    {u phi : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContinuousOn u (closedBall a R))
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ ball a r)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (t : ℝ)
    (hrange0 : MapsTo u (closedBall a R) K)
    (hranget : MapsTo (fun p => u p + t • phi p) (closedBall a R) K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiffOn ℝ 1 F O) :
    MemW1p 2 (fun p => F (u p + t • phi p) - F (u p)) univ ∧
      ∀ p, p ∉ tsupport phi → F (u p + t • phi p) - F (u p) = 0 := by
  have h0 := m64WeakCoordinates_scalar_memW1p hr hrR hu hW hw hO hK hKO hrange0 hF
  obtain ⟨hut, hWt, hwt⟩ := m64_affine_weak_coordinates hu hphi hW hw t
  have ht := m64WeakCoordinates_scalar_memW1p hr hrR hut hWt hwt hO hK hKO hranget hF
  have hdiff : MemWkp 1 2 (fun p => F (u p + t • phi p) - F (u p)) (ball a r) := by
    exact MemWkp.sub (by norm_num) isOpen_ball
      (MemWkp.one_iff_memW1p.mpr ht) (MemWkp.one_iff_memW1p.mpr h0)
  obtain ⟨chi, hchi, hchic, -, hchione, hchis⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      hc isOpen_ball hs
  have hdiff' : MemWkp 1 2 (fun p => F (u p + t • phi p) - F (u p))
      (ball a r ∩ univ) := by simpa only [inter_univ] using hdiff
  have hglobal :=
    Poincare.Analysis.Sobolev.BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset
      1 isOpen_univ isOpen_ball hdiff' hchi hchic hchis
  have hzero (p : LoopPlane) (hp : p ∉ tsupport phi) :
      F (u p + t • phi p) - F (u p) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport hp, smul_zero, add_zero, sub_self]
  have heq : (fun p => chi p * (F (u p + t • phi p) - F (u p))) =
      fun p => F (u p + t • phi p) - F (u p) := by
    funext p
    by_cases hp : p ∈ tsupport phi
    · rw [hchione p hp, one_mul]
    · rw [hzero p hp, mul_zero]
  rw [heq] at hglobal
  exact ⟨MemWkp.one_iff_memW1p.mp hglobal, hzero⟩

end PoincareConjecture
