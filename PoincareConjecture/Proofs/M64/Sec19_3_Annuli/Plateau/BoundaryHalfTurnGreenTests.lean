import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnTestLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularSlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "a" => curvePeriod / 2
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)

theorem m64HalfTurnPiece_vertical_green
    {u V : LoopPlane → E} (hu : Integrable u mu) (hV : Integrable V mu)
    {c0 c1 : ℝ → E} (hc0 : IntegrableOn c0 I volume) (hc1 : IntegrableOn c1 I volume)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p (ei 1) • u p) =
        ∫ x in I, phi (annulusPoint x 1) • c1 x - phi (annulusPoint x 0) • c0 x)
    {f g : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (∫ p in S, m64HalfTurnPiece f g p • V p) +
      (∫ p in S, m64HalfTurnPiece (fun q => fderiv ℝ f q (ei 1))
        (fun q => fderiv ℝ g q (ei 1)) p • u p) =
      ∫ x in I, m64HalfTurnPiece f g (annulusPoint x 1) • c1 x -
        m64HalfTurnPiece f g (annulusPoint x 0) • c0 x := by
  have hl := (m64HalfTurnBlend_integral_tendsto measurable_id m64HalfTurn_rectangle_ae.1
    m64HalfTurn_rectangle_ae.2 hV hf hg).add
      (m64HalfTurnBlend_derivative_integral_tendsto measurable_id
        m64HalfTurn_rectangle_ae.1 m64HalfTurn_rectangle_ae.2 hu hf hg 1 (Or.inl rfl))
  obtain ⟨C, hC0, hC⟩ := m64HalfTurnBlend_bound hf.continuous hg.continuous
  have hr : Tendsto (fun j => ∫ x in I,
      m64HalfTurnBlend j f g (annulusPoint x 1) • c1 x -
        m64HalfTurnBlend j f g (annulusPoint x 0) • c0 x) atTop
      (𝓝 (∫ x in I, m64HalfTurnPiece f g (annulusPoint x 1) • c1 x -
        m64HalfTurnPiece f g (annulusPoint x 0) • c0 x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => C * (‖c1 x‖ + ‖c0 x‖))
    · intro j
      have hm (s : ℝ) : AEStronglyMeasurable
          (fun x => m64HalfTurnBlend j f g (annulusPoint x s)) (volume.restrict I) :=
        ((m64HalfTurnBlend_contDiff hf hg j).continuous.comp
          (m64Source_annulusPoint_contDiff s).continuous).aestronglyMeasurable
      exact ((hm 1).smul hc1.aestronglyMeasurable).sub ((hm 0).smul hc0.aestronglyMeasurable)
    · exact (hc1.norm.add hc0.norm).const_mul C
    · intro j
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have h0 : annulusPoint x 0 ∈ m64AnnulusDomain := ⟨hx.1, hx.2, le_rfl, zero_le_one⟩
      have h1 : annulusPoint x 1 ∈ m64AnnulusDomain := ⟨hx.1, hx.2, zero_le_one, le_rfl⟩
      calc
        _ ≤ ‖m64HalfTurnBlend j f g (annulusPoint x 1) • c1 x‖ +
            ‖m64HalfTurnBlend j f g (annulusPoint x 0) • c0 x‖ := norm_sub_le _ _
        _ ≤ C * ‖c1 x‖ + C * ‖c0 x‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul_of_nonneg_right (hC j _ h1) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hC j _ h0) (norm_nonneg _))
        _ = _ := by ring
    · filter_upwards [(m64HalfTurn_boundary_ae (s := 0) ⟨le_rfl, zero_le_one⟩).2] with x hx
      have h0 : annulusPoint x 0 0 ≠ a := hx
      have h1 : annulusPoint x 1 0 ≠ a := hx
      apply tendsto_const_nhds.congr'
      filter_upwards [m64HalfTurnBlend_eventually hf hg h0 1,
        m64HalfTurnBlend_eventually hf hg h1 1] with j hj0 hj1
      rw [hj0.1, hj1.1]
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall fun j =>
    (hgreen _ (m64HalfTurnBlend_contDiff hf hg j)).symm)

theorem m64HalfTurnPiece_seam_green
    {u V : LoopPlane → E} (hu : Integrable u mu) (hV : Integrable V mu) (D : E)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p (ei 0) • u p) =
        (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) • D)
    {f g : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hmatch : ∀ s ∈ Icc (0 : ℝ) 1, f (annulusPoint a s) = g (annulusPoint a s))
    (hend : ∀ s ∈ Icc (0 : ℝ) 1,
      g (annulusPoint curvePeriod s) = f (annulusPoint 0 s)) :
    (∫ p in S, m64HalfTurnPiece f g p • V p) +
      (∫ p in S, m64HalfTurnPiece (fun q => fderiv ℝ f q (ei 0))
        (fun q => fderiv ℝ g q (ei 0)) p • u p) =
      (∫ s in Icc (0 : ℝ) 1, g (annulusPoint curvePeriod s)) • D := by
  have hl := (m64HalfTurnBlend_integral_tendsto measurable_id m64HalfTurn_rectangle_ae.1
    m64HalfTurn_rectangle_ae.2 hV hf hg).add
      (m64HalfTurnBlend_derivative_integral_tendsto measurable_id
        m64HalfTurn_rectangle_ae.1 m64HalfTurn_rectangle_ae.2 hu hf hg 0 (Or.inr hmatch))
  have hseq (j : ℕ) :
      (∫ p in S, m64HalfTurnBlend j f g p • V p) +
        (∫ p in S, fderiv ℝ (m64HalfTurnBlend j f g) p (ei 0) • u p) =
      (∫ s in Icc (0 : ℝ) 1, g (annulusPoint curvePeriod s)) • D := by
    have h := hgreen _ (m64HalfTurnBlend_contDiff hf hg j) (by
      intro s hs
      rw [(m64HalfTurnBlend_endpoints j s).1, (m64HalfTurnBlend_endpoints j s).2]
      exact hend s hs)
    simpa only [(m64HalfTurnBlend_endpoints j _).2] using h
  apply tendsto_nhds_unique hl
  exact tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hseq j).symm)

end PoincareConjecture
