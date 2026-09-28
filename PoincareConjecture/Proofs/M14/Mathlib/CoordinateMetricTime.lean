import PoincareConjecture.Proofs.M09.CoordinateConnectionTime
import PoincareConjecture.Proofs.M09.CoordinateCompatibility










set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

open PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem coordinateMetric_time_compatible
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (hsym : ∀ z ∈ U, ∀ v w : E, G z v w = G z w v)
    (s : ℝ) (y : E) (hz : (s, y) ∈ U) (v a w : E) :
    let C := coordinateConnectionBilinear G
    let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun q => fderiv ℝ G (s, q) (1, 0)
    fderiv ℝ H y v a w - H y (C (s, y) v a) w - H y a (C (s, y) v w) =
      G (s, y) (fderiv ℝ C (s, y) (1, 0) v a) w +
        G (s, y) (fderiv ℝ C (s, y) (1, 0) v w) a := by
  let C := coordinateConnectionBilinear G
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun q => fderiv ℝ G (s, q) (1, 0)
  have hGa := hG.contDiffAt (hU.mem_nhds hz)
  have hHa : ContDiffAt ℝ ∞ H y :=
    ((hGa.fderiv_right (m := ∞) (by simp)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
  have hHsym : ∀ᶠ q in 𝓝 y, ∀ b c : E, H q b c = H q c b := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hz)] with q hq
    apply fderiv_bilinear_symm G (s, q)
      ((hG.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
    filter_upwards [hU.mem_nhds hq] with z hz'
    exact hsym z hz'
  have hDsym := fderiv_bilinear_symm H y (hHa.differentiableAt (by simp)) hHsym v w a
  have hfirst := coordinateConnection_time_pairing G U hU hG hpos s y hz v a w
  have hsecond := coordinateConnection_time_pairing G U hU hG hpos s y hz v w a
  change G (s, y) (fderiv ℝ C (s, y) (1, 0) v a) w =
    (1 / 2 : ℝ) * (fderiv ℝ H y v a w + fderiv ℝ H y a v w - fderiv ℝ H y w v a) -
      H y (C (s, y) v a) w at hfirst
  change G (s, y) (fderiv ℝ C (s, y) (1, 0) v w) a =
    (1 / 2 : ℝ) * (fderiv ℝ H y v w a + fderiv ℝ H y w v a - fderiv ℝ H y a v w) -
      H y (C (s, y) v w) a at hsecond
  rw [hDsym, hHsym.self_of_nhds (C (s, y) v w) a] at hsecond
  dsimp only
  change fderiv ℝ H y v a w - H y (C (s, y) v a) w - H y a (C (s, y) v w) = _
  linarith

end PoincareConjecture.M14
