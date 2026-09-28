import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurvatureMotion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ShrinkingCurveBoundaryMotion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusBoundaryImmersion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64Annulus_exists_fixed_metric_forward_of_shrinking_curves
    (F : RicciFlow n M (Icc a b)) {c0 c1 : ℝ → ℝ → M}
    (hc0 : M62ShrinkingCurve F c0) (hc1 : M62ShrinkingCurve F c1)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (A : M64Annulus (F.metric t) (fun x => c0 x t) (fun x => c1 x t))
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (F.metric t) A.map p 0 0 = m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, (F.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (F.metric t) (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area + h * (K * A.area + eta) := by
  obtain ⟨epsilon0, hepsilon0, f0, hf0, hp0, ha0, hv0⟩ :=
    m64ShrinkingCurve_exists_centered_boundary_motion F hc0 ht
  obtain ⟨epsilon1, hepsilon1, f1, hf1, hp1, ha1, hv1⟩ :=
    m64ShrinkingCurve_exists_centered_boundary_motion F hc1 ht
  let epsilon := min epsilon0 epsilon1
  have hepsilon : 0 < epsilon := lt_min hepsilon0 hepsilon1
  have hsub0 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsub1 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon1) epsilon1 :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hinit0 (x : ℝ) : f0 0 x = c0 x t := by
    simpa only [add_zero] using ha0 0 (hsub0 hzero) x
  have hinit1 (x : ℝ) : f1 0 x = c1 x t := by
    simpa only [add_zero] using ha1 0 (hsub1 hzero) x
  have hpoint {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod)
      (hs : s ∈ Icc (0 : ℝ) 1) : annulusPoint x s ∈ m64AnnulusDomain := by
    change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
    exact ⟨hx.1, hx.2, hs⟩
  have hlower (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x 0) := by
    apply m64Annulus_energyDensity_pos_of_horizontal_immersed (F.metric t)
      ((hA.contMDiffAt (hO.mem_nhds (hdom (hpoint hx (by simp))))).mdifferentiableAt
        (by simp))
    have heq : (fun y => A.map (annulusPoint y 0)) = (fun y => c0 y t) :=
      funext A.lower_boundary
    rw [heq]
    exact hc0.immersed t (Ioo_subset_Icc_self ht) x
  have hupper (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x 1) := by
    apply m64Annulus_energyDensity_pos_of_horizontal_immersed (F.metric t)
      ((hA.contMDiffAt (hO.mem_nhds (hdom (hpoint hx (by simp))))).mdifferentiableAt
        (by simp))
    have heq : (fun y => A.map (annulusPoint y 1)) = (fun y => c1 y t) :=
      funext A.upper_boundary
    rw [heq]
    exact hc1.immersed t (Ioo_subset_Icc_self ht) x
  have hforward := m64Annulus_exists_forward_competitors_of_curvature_motion F A
    hminimum hconformal hO hdom hA hK hsec hlower hupper hepsilon f0 f1
    (hf0.mono (prod_mono_left hsub0)) (hf1.mono (prod_mono_left hsub1))
    hinit0 hinit1 hp0 hp1 hv0 hv1
  intro eta heta
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon) epsilon :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hzero)
  filter_upwards [hforward eta heta, htime] with h hh htime
  have he0 : f0 h = (fun x => c0 x (t + h)) := funext (ha0 h (hsub0 htime))
  have he1 : f1 h = (fun x => c1 x (t + h)) := funext (ha1 h (hsub1 htime))
  exact he0 ▸ he1 ▸ hh

end PoincareConjecture
