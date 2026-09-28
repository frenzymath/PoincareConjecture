import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M28

theorem tendstoUniformlyOn_edist_toReal_of_mutual_inner_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (gseq : ℕ → RiemannianMetric n M)
    (S : Set M) {B : ℝ} (hB : 0 ≤ B)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, g.edist x y ≤ ENNReal.ofReal B)
    (hcompare : ∀ c : ℝ, 1 < c → ∀ᶠ k in atTop, ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (gseq k).inner x v v ≤ c ^ 2 * g.inner x v v ∧
        g.inner x v v ≤ c ^ 2 * (gseq k).inner x v v) :
    TendstoUniformlyOn (fun k (p : M × M) => ((gseq k).edist p.1 p.2).toReal)
      (fun p => (g.edist p.1 p.2).toReal) atTop (S ×ˢ S) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  let c : ℝ := 1 + eta / (2 * (B + 1))
  have hden : 0 < 2 * (B + 1) := by positivity
  have hc : 1 < c := by
    dsimp only [c]
    exact lt_add_of_pos_right _ (div_pos heta hden)
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hsmall : (c - 1) * B < eta := by
    calc
      (c - 1) * B < (c - 1) * (2 * (B + 1)) :=
        mul_lt_mul_of_pos_left (by linarith) (sub_pos.mpr hc)
      _ = eta := by
        dsimp only [c]
        rw [add_sub_cancel_left, div_mul_cancel₀ _ hden.ne']
  filter_upwards [hcompare c hc] with k hk
  intro p hp
  have hforward : (gseq k).edist p.1 p.2 ≤ ENNReal.ofReal c * g.edist p.1 p.2 := by
    simpa only [id_eq] using g.edist_le_mul_of_inner_mfderiv_le (gseq k)
      (F := id) contMDiff_id hcpos (fun x v => by
        simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using (hk x v).1) p.1 p.2
  have hreverse : g.edist p.1 p.2 ≤ ENNReal.ofReal c * (gseq k).edist p.1 p.2 := by
    simpa only [id_eq] using (gseq k).edist_le_mul_of_inner_mfderiv_le g
      (F := id) contMDiff_id hcpos (fun x v => by
        simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using (hk x v).2) p.1 p.2
  have hgfinite : g.edist p.1 p.2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam p.1 hp.1 p.2 hp.2)
  have hfactor : ENNReal.ofReal c * g.edist p.1 p.2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgfinite
  have hseqfinite : (gseq k).edist p.1 p.2 ≠ ⊤ :=
    ne_top_of_le_ne_top hfactor hforward
  have hu : ((gseq k).edist p.1 p.2).toReal ≤ c * (g.edist p.1 p.2).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le] using
      ENNReal.toReal_mono hfactor hforward
  have hl : (g.edist p.1 p.2).toReal ≤ c * ((gseq k).edist p.1 p.2).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hseqfinite) hreverse
  have hdB : (g.edist p.1 p.2).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam p.1 hp.1 p.2 hp.2)
  have habs : |((gseq k).edist p.1 p.2).toReal - (g.edist p.1 p.2).toReal| ≤
      (c - 1) * B := by
    apply abs_le.mpr
    constructor
    · by_cases hseqB : ((gseq k).edist p.1 p.2).toReal ≤ B
      · nlinarith [mul_nonneg (sub_nonneg.mpr hc.le) (sub_nonneg.mpr hseqB)]
      · have hnonneg : 0 ≤ (c - 1) * B := mul_nonneg (sub_nonneg.mpr hc.le) hB
        linarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.le) (sub_nonneg.mpr hdB)]
  simpa only [Real.dist_eq, abs_sub_comm] using habs.trans_lt hsmall

end PoincareConjecture.M28
