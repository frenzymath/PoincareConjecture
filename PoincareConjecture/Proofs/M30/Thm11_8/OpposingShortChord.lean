import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Ray










set_option autoImplicit false

open Set
open Poincare.Riemannian.Soul
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M30



theorem not_short_chord_of_opposing_vertices
    {n : ℕ} {M : Type u} [MetricSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hcomplete : MetricComplete g)
    (hsec : D.NonnegativeSectionalCurvature)
    {gamma sigma : ℝ → M} {d L a b ell : ℝ}
    (hd : 0 < d) (hL : 0 ≤ L) (hLsmall : L ≤ d / 2)
    (ha : d ≤ a) (haUpper : a ≤ d + L)
    (hb : d ≤ b) (hbUpper : b ≤ d + L)
    (hgamma : IsMinimizingOn gamma (Icc 0 a))
    (hsigma : IsMinimizingOn sigma (Icc 0 b))
    (hbase : gamma 0 = sigma 0)
    (hend : 2 * d ≤ dist (gamma a) (sigma b))
    (hell : 0 < ell) (hellA : ell ≤ a) (hellB : ell ≤ b)
    (hchord : dist (gamma ell) (sigma ell) ≤ ell / 2) : False := by
  have haPos : 0 < a := hd.trans_le ha
  have hbPos : 0 < b := hd.trans_le hb
  have hgammaEdist : ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
      g.edist (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
    intro s hs t ht
    rw [← hgamma hs ht, hdist, ENNReal.ofReal_toReal (g.edist_ne_top _ _)]
  have hsigmaEdist : ∀ s ∈ Icc (0 : ℝ) b, ∀ t ∈ Icc (0 : ℝ) b,
      g.edist (sigma s) (sigma t) = ENNReal.ofReal |s - t| := by
    intro s hs t ht
    rw [← hsigma hs ht, hdist, ENNReal.ofReal_toReal (g.edist_ne_top _ _)]
  have hcompare := g.toponogov_corresponding_side_of_edist_segments D hcomplete hsec
    haPos hbPos rfl hbase.symm hgammaEdist hsigmaEdist
    ell ⟨hell.le, hellA⟩ ell ⟨hell.le, hellB⟩
  rw [← hdist, ← hdist] at hcompare
  let c := dist (gamma a) (sigma b)
  let e := dist (gamma ell) (sigma ell)
  change ell ^ 2 + ell ^ 2 - 2 * ell * ell *
    ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ≤ e ^ 2 at hcompare
  have hden : 0 < 2 * a * b := by positivity
  have heSquare : e ^ 2 ≤ ell ^ 2 / 4 := by
    have hsq := mul_self_le_mul_self (show 0 ≤ e from dist_nonneg) hchord
    nlinarith
  have hcleared : (ell ^ 2 + ell ^ 2) * (2 * a * b) -
      2 * ell * ell * (a ^ 2 + b ^ 2 - c ^ 2) ≤ e ^ 2 * (2 * a * b) := by
    calc
      _ = (ell ^ 2 + ell ^ 2 - 2 * ell * ell *
          ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b))) * (2 * a * b) := by
        field_simp [haPos.ne', hbPos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hcompare hden.le
  have hscaled : ell ^ 2 * c ^ 2 ≤
      ell ^ 2 * ((a - b) ^ 2 + a * b / 4) := by
    have hupper := mul_le_mul_of_nonneg_right heSquare hden.le
    nlinarith
  have hc : c ^ 2 ≤ (a - b) ^ 2 + a * b / 4 :=
    le_of_mul_le_mul_left hscaled (sq_pos_of_pos hell)
  have habDiff : |a - b| ≤ d / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have habSquare : (a - b) ^ 2 ≤ d ^ 2 / 4 := by
    have hsq := mul_self_le_mul_self (abs_nonneg (a - b)) habDiff
    nlinarith [sq_abs (a - b)]
  have habProduct : a * b ≤ 9 * d ^ 2 / 4 := by
    have hupper : d + L ≤ 3 * d / 2 := by linarith
    have hsq := mul_self_le_mul_self (add_nonneg hd.le hL) hupper
    calc
      a * b ≤ (d + L) * (d + L) :=
        mul_le_mul haUpper hbUpper hbPos.le (add_nonneg hd.le hL)
      _ ≤ 9 * d ^ 2 / 4 := by nlinarith
  have hcLower : 4 * d ^ 2 ≤ c ^ 2 := by
    have hsq := mul_self_le_mul_self (show 0 ≤ 2 * d by positivity) hend
    nlinarith
  nlinarith [sq_pos_of_pos hd]

end PoincareConjecture.M30
