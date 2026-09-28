import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CylinderModulusBound

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64WeightedGramEnergy_ge_phase_degree
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (f : LoopPlane → P.charts.Point) (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f)
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L)
    (hquot : ∀ p, P.circle.quotient (L p) = (f p).2)
    {d : ℝ} (hd : d ≠ 0)
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) =
      L (annulusPoint x s) + d)
    {r E : ℝ} (hr : 0 < r)
    (hE : (∫ p in interior m64AnnulusDomain,
      (r * m60AreaGram (P.flow.metric t) f p 0 0 +
        r⁻¹ * m60AreaGram (P.flow.metric t) f p 1 1) / 2) ≤ E) :
    r * d ^ 2 / (2 * curvePeriod) ≤ E := by
  have hbound := m64CirclePhase_cylinder_modulus_bound P t f hf L hL hquot hd hshift hr hE
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hden : 0 < 2 * curvePeriod := by positivity
  apply (div_le_iff₀ hden).mpr
  have hh : r * d ^ 2 ≤ (2 * curvePeriod * E) :=
    (le_div_iff₀ hd2).mp hbound
  nlinarith

end PoincareConjecture
