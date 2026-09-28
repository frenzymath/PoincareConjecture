import PoincareConjecture.Proofs.M35.CapGeometry.RadialCapNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace

private theorem inverse_half_eq (Q : ℝ) (hQ : 0 < Q) :
    Q ^ (-1 / 2 : ℝ) = (Real.sqrt Q)⁻¹ := by
  rw [neg_div, Real.rpow_neg hQ.le, ← Real.sqrt_eq_rpow]

private theorem inverse_half_cube (Q : ℝ) (hQ : 0 < Q) :
    (Q ^ (-1 / 2 : ℝ)) ^ 3 = Q ^ (-3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
  norm_num

private theorem three_halves_eq (Q : ℝ) (hQ : 0 < Q) :
    Q ^ (3 / 2 : ℝ) = Q * Real.sqrt Q := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hQ, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem exists_radial_cap_analytic_constant {m M L : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hL : 0 < L) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀,
      ∀ (g : RiemannianMetric 3 V) (D : LeviCivitaData g) (Q R : ℝ),
        0 < Q → 0 < R → R ≤ L / Real.sqrt Q →
        (∀ y ∈ g.ball 0 R,
          m * Q ≤ D.scalarCurvature y ∧ D.scalarCurvature y ≤ M * Q ∧
          scalarGradientNorm g D y ≤ M * (Q * Real.sqrt Q) ∧
          |D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y| ≤ M * Q ^ 2) →
        (∀ y ∈ g.ball 0 R, ∀ z ∈ g.ball 0 R,
          D.scalarCurvature z < C * D.scalarCurvature y) ∧
        2 * R ≤ C * scalarCurvatureSupOn g D (g.ball 0 R) ^ (-1 / 2 : ℝ) ∧
        R ^ 3 * (Real.pi * 4 / 3) <
          C * scalarCurvatureSupOn g D (g.ball 0 R) ^ (-3 / 2 : ℝ) ∧
        (∀ y ∈ g.ball 0 R,
          scalarGradientNorm g D y < C * D.scalarCurvature y ^ (3 / 2 : ℝ)) ∧
        (∀ y ∈ g.ball 0 R,
          |D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y| <
            C * D.scalarCurvature y ^ 2) := by
  let d := M ^ (-1 / 2 : ℝ)
  let v := M ^ (-3 / 2 : ℝ)
  let p := m ^ (3 / 2 : ℝ)
  let W := L ^ 3 * (Real.pi * 4 / 3)
  have hd : 0 < d := Real.rpow_pos_of_pos hM _
  have hv : 0 < v := Real.rpow_pos_of_pos hM _
  have hp : 0 < p := Real.rpow_pos_of_pos hm _
  have hW : 0 < W := by dsimp only [W]; positivity
  let Cr := M / m
  let Cd := 2 * L / d
  let Cv := W / v
  let Cg := M / p
  let Ce := M / m ^ 2
  have hCr : 0 < Cr := div_pos hM hm
  have hCd : 0 < Cd := div_pos (mul_pos (by norm_num) hL) hd
  have hCv : 0 < Cv := div_pos hW hv
  have hCg : 0 < Cg := div_pos hM hp
  have hCe : 0 < Ce := div_pos hM (sq_pos_of_pos hm)
  let C₀ := Cr + Cd + Cv + Cg + Ce + 1
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro C hCC g D Q R hQ hR hradius hbounds
  have hC : 0 < C := hC₀.trans_le hCC
  have hrC : Cr < C := by
    dsimp only [C₀] at hCC
    linarith only [hCC, hCd, hCv, hCg, hCe]
  have hdC : Cd < C := by
    dsimp only [C₀] at hCC
    linarith only [hCC, hCr, hCv, hCg, hCe]
  have hvC : Cv < C := by
    dsimp only [C₀] at hCC
    linarith only [hCC, hCr, hCd, hCg, hCe]
  have hgC : Cg < C := by
    dsimp only [C₀] at hCC
    linarith only [hCC, hCr, hCd, hCv, hCe]
  have heC : Ce < C := by
    dsimp only [C₀] at hCC
    linarith only [hCC, hCr, hCd, hCv, hCg]
  have hrconstant : M < C * m := (div_lt_iff₀ hm).mp hrC
  have hdconstant : 2 * L < C * d := (div_lt_iff₀ hd).mp hdC
  have hvconstant : W < C * v := (div_lt_iff₀ hv).mp hvC
  have hgconstant : M < C * p := (div_lt_iff₀ hp).mp hgC
  have heconstant : M < C * m ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hm)).mp heC
  have hzero : (0 : V) ∈ g.ball 0 R := by
    change g.edist 0 0 < ENNReal.ofReal R
    rw [show g.edist 0 0 = 0 from @edist_self V g.toEMetricSpace.toPseudoEMetricSpace 0]
    exact ENNReal.ofReal_pos.mpr hR
  let S := scalarCurvatureSupOn g D (g.ball 0 R)
  have hbounded : BddAbove (range fun z : g.ball 0 R => D.scalarCurvature z.1) := by
    refine ⟨M * Q, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (hbounds z z.property).2.1
  have hSpos : 0 < S := (mul_pos hm hQ).trans_le
    ((hbounds 0 hzero).1.trans (le_csSup hbounded ⟨⟨0, hzero⟩, rfl⟩))
  have hSupper : S ≤ M * Q := by
    change sSup (range fun z : g.ball 0 R => D.scalarCurvature z.1) ≤ M * Q
    apply csSup_le (s := range fun z : g.ball 0 R => D.scalarCurvature z.1)
      ⟨D.scalarCurvature 0, ⟨⟨0, hzero⟩, rfl⟩⟩
    rintro _ ⟨z, rfl⟩
    exact (hbounds z z.property).2.1
  let u := Q ^ (-1 / 2 : ℝ)
  let w := Q ^ (-3 / 2 : ℝ)
  have hu : 0 < u := Real.rpow_pos_of_pos hQ _
  have hw : 0 < w := Real.rpow_pos_of_pos hQ _
  have hRu : R ≤ L * u := by
    simpa only [u, inverse_half_eq Q hQ, div_eq_mul_inv] using hradius
  have hu3 : u ^ 3 = w := inverse_half_cube Q hQ
  have hdS : d * u ≤ S ^ (-1 / 2 : ℝ) := by
    dsimp only [d, u]
    rw [← Real.mul_rpow hM.le hQ.le]
    exact Real.rpow_le_rpow_of_nonpos hSpos hSupper (by norm_num)
  have hvS : v * w ≤ S ^ (-3 / 2 : ℝ) := by
    dsimp only [v, w]
    rw [← Real.mul_rpow hM.le hQ.le]
    exact Real.rpow_le_rpow_of_nonpos hSpos hSupper (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy z hz
    calc
      D.scalarCurvature z ≤ M * Q := (hbounds z hz).2.1
      _ < (C * m) * Q := mul_lt_mul_of_pos_right hrconstant hQ
      _ = C * (m * Q) := mul_assoc _ _ _
      _ ≤ C * D.scalarCurvature y := mul_le_mul_of_nonneg_left (hbounds y hy).1 hC.le
  · change 2 * R ≤ C * S ^ (-1 / 2 : ℝ)
    calc
      2 * R ≤ 2 * (L * u) := mul_le_mul_of_nonneg_left hRu (by norm_num)
      _ = (2 * L) * u := (mul_assoc _ _ _).symm
      _ ≤ (C * d) * u := (mul_lt_mul_of_pos_right hdconstant hu).le
      _ = C * (d * u) := mul_assoc _ _ _
      _ ≤ C * S ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hdS hC.le
  · change R ^ 3 * (Real.pi * 4 / 3) < C * S ^ (-3 / 2 : ℝ)
    have hvol : R ^ 3 * (Real.pi * 4 / 3) ≤ W * w := by
      calc
        R ^ 3 * (Real.pi * 4 / 3) ≤ (L * u) ^ 3 * (Real.pi * 4 / 3) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hRu 3) (by positivity)
        _ = W * w := by rw [mul_pow, hu3]; dsimp only [W]; ring
    exact hvol.trans_lt ((mul_lt_mul_of_pos_right hvconstant hw).trans_le (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hvS hC.le))
  · intro y hy
    have hscale : 0 < Q * Real.sqrt Q := mul_pos hQ (Real.sqrt_pos.mpr hQ)
    have hfloor : p * (Q * Real.sqrt Q) ≤ D.scalarCurvature y ^ (3 / 2 : ℝ) := by
      have hh := Real.rpow_le_rpow (mul_pos hm hQ).le (hbounds y hy).1
        (show (0 : ℝ) ≤ 3 / 2 by norm_num)
      simpa only [Real.mul_rpow hm.le hQ.le, three_halves_eq Q hQ, p] using hh
    calc
      scalarGradientNorm g D y ≤ M * (Q * Real.sqrt Q) := (hbounds y hy).2.2.1
      _ < (C * p) * (Q * Real.sqrt Q) := mul_lt_mul_of_pos_right hgconstant hscale
      _ = C * (p * (Q * Real.sqrt Q)) := mul_assoc _ _ _
      _ ≤ C * D.scalarCurvature y ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hfloor hC.le
  · intro y hy
    have hfloor : m ^ 2 * Q ^ 2 ≤ D.scalarCurvature y ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (mul_pos hm hQ).le (hbounds y hy).1 2
    calc
      |D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y| ≤ M * Q ^ 2 :=
        (hbounds y hy).2.2.2
      _ < (C * m ^ 2) * Q ^ 2 :=
        mul_lt_mul_of_pos_right heconstant (sq_pos_of_pos hQ)
      _ = C * (m ^ 2 * Q ^ 2) := mul_assoc _ _ _
      _ ≤ C * D.scalarCurvature y ^ 2 := mul_le_mul_of_nonneg_left hfloor hC.le

end PoincareConjecture.M35.Uniqueness
