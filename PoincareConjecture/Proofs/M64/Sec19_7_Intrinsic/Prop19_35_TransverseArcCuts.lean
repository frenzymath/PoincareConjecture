import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardBandChain

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem quarterTurn_components (w : AnnulusCoordinates) :
    quarterTurn w 0 = -w 1 ∧ quarterTurn w 1 = w 0 := by
  simp [quarterTurn_apply, Complex.orthonormalBasisOneI_repr_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]

private theorem transverse_inner (u w : AnnulusCoordinates) :
    inner ℝ (-quarterTurn w) u = inner ℝ (quarterTurn u) w := by
  have hu := quarterTurn_components u
  have hw := quarterTurn_components w
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    hu.1, hu.2, hw.1, hw.2]
  ring

theorem m64Intrinsic_graph_transverse_direction
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {v : AnnulusCoordinates} (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hL : ∀ w, L w = (inner ℝ v w, inner ℝ (quarterTurn v) w))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hf : ContDiffOn ℝ ∞ f G.target)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hpos : 0 < (L (deriv gamma t)).1)
    {w : AnnulusCoordinates} (hw : 0 < inner ℝ (quarterTurn (deriv gamma t)) w) :
    0 < (L w).2 - deriv f (G t) * (L w).1 ∧
      inner ℝ (-quarterTurn w) w = 0 ∧
      0 < inner ℝ (-quarterTurn w) (L.symm (1, deriv f (G t))) := by
  have htan := m64Intrinsic_graph_tangent hg L G hG hf hgraph ht
  have hfirst := congrArg Prod.fst htan
  simp only [Prod.smul_fst, smul_eq_mul, mul_one] at hfirst
  have hd : 0 < deriv G t := hfirst ▸ hpos
  have hv : v ≠ 0 := by
    intro hz
    simp only [hL, hz, inner_zero_left] at hpos
    exact (lt_irrefl 0) hpos
  have hdet : (L (deriv gamma t)).1 * (L w).2 -
      (L (deriv gamma t)).2 * (L w).1 =
      inner ℝ v v * inner ℝ (quarterTurn (deriv gamma t)) w := by
    rw [hL, hL]
    have hv' := quarterTurn_components v
    have ht' := quarterTurn_components (deriv gamma t)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      star_trivial, hv'.1, hv'.2, ht'.1, ht'.2]
    ring
  have hpositive := mul_pos (real_inner_self_pos.mpr hv) hw
  have hproduct : 0 < deriv G t * ((L w).2 - deriv f (G t) * (L w).1) := by
    rw [htan] at hdet
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one] at hdet
    nlinarith only [hdet, hpositive]
  refine ⟨(mul_pos_iff_of_pos_left hd).mp hproduct, ?_, ?_⟩
  · rw [inner_neg_left, real_inner_comm, inner_quarterTurn_self, neg_zero]
  · have hvector : deriv gamma t = deriv G t • L.symm (1, deriv f (G t)) := by
      apply L.injective
      simpa only [map_smul, L.apply_symm_apply] using htan
    have hsep : 0 < inner ℝ (-quarterTurn w) (deriv gamma t) := by
      rwa [transverse_inner]
    rw [hvector, real_inner_smul_right] at hsep
    exact (mul_pos_iff_of_pos_left hd).mp hsep

theorem m64Intrinsic_exists_arc_transverse_graph
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) {v : AnnulusCoordinates}
    (hpos : ∀ t ∈ Icc a b, 0 < inner ℝ v (deriv gamma t))
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t)) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : OpenPartialHomeomorph ℝ ℝ) (f : ℝ → ℝ),
      Icc a b ⊆ G.source ∧ StrictMonoOn G G.source ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ f G.target ∧
      (∀ t ∈ G.source, L (gamma t) = (G t, f (G t))) ∧
      G '' Icc a b = Icc (G a) (G b) ∧ Icc (G a) (G b) ⊆ G.target ∧
      (∀ t ∈ Icc a b,
        0 < (L (d t)).2 - deriv f (G t) * (L (d t)).1 ∧
        inner ℝ (-quarterTurn (d t)) (d t) = 0 ∧
        0 < inner ℝ (-quarterTurn (d t)) (L.symm (1, deriv f (G t)))) ∧
      Nonempty (TransverseGraphCuts f (G a) (G b)
        (L (d a)).1 (L (d a)).2 (L (d b)).1 (L (d b)).2) := by
  obtain ⟨l, u, G, L, f, hla, hbu, hsource, hGval, hL, hmono, hG,
    _, _, hf, hgraph, himage, htarget, _⟩ :=
    exists_graph_coordinates_of_positive_projection hg hab.le hpos
  have hI : Icc a b ⊆ G.source := by
    rw [hsource]
    exact fun _ ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hbu⟩
  have hmonoG : StrictMonoOn G G.source := by
    intro x hx y hy hxy
    simpa only [hGval] using hmono hx hy hxy
  have htrans (t : ℝ) (ht : t ∈ Icc a b) := m64Intrinsic_graph_transverse_direction
    hg L hL G hG hf hgraph (hI ht)
    (show 0 < (L (deriv gamma t)).1 by simpa only [hL] using hpos t ht) (hd t ht)
  refine ⟨L, G, f, hI, hmonoG, hG, hf, hgraph, himage, htarget, htrans, ?_⟩
  have ha := hI (left_mem_Icc.mpr hab.le)
  have hb := hI (right_mem_Icc.mpr hab.le)
  exact exists_transverseGraphCuts G.open_target hf G.open_target hf
    (hmonoG ha hb hab) (G.map_source ha) (G.map_source hb)
    (htrans a (left_mem_Icc.mpr hab.le)).1 (htrans b (right_mem_Icc.mpr hab.le)).1

theorem m64Intrinsic_exists_arc_transverse_cut_subdivision
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t)) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      ∀ i : Fin n,
        Icc (c i.castSucc) (c i.succ) ⊆ (G i).source ∧
        StrictMonoOn (G i) (G i).source ∧
        ContDiffOn ℝ ∞ (G i) (G i).source ∧
        ContDiffOn ℝ ∞ (f i) (G i).target ∧
        (∀ t ∈ (G i).source, L i (gamma t) = (G i t, f i (G i t))) ∧
        G i '' Icc (c i.castSucc) (c i.succ) =
          Icc (G i (c i.castSucc)) (G i (c i.succ)) ∧
        Icc (G i (c i.castSucc)) (G i (c i.succ)) ⊆ (G i).target ∧
        (∀ t ∈ Icc (c i.castSucc) (c i.succ),
          0 < (L i (d t)).2 - deriv (f i) (G i t) * (L i (d t)).1 ∧
          inner ℝ (-quarterTurn (d t)) (d t) = 0 ∧
          0 < inner ℝ (-quarterTurn (d t)) ((L i).symm (1, deriv (f i) (G i t)))) ∧
        Nonempty (TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
          (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
          (L i (d (c i.succ))).1 (L i (d (c i.succ))).2) := by
  obtain ⟨n, c, v, hn, hc, hfirst, hlast, hv⟩ :=
    exists_finite_strictMono_projection_subdivision hg hab hregular
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hpieces (i : Fin n) := m64Intrinsic_exists_arc_transverse_graph hg
    (hc Fin.castSucc_lt_succ) (hv i).2.2.1 d
    (fun t ht => hd t ⟨(hcut i.castSucc).1.trans ht.1, ht.2.trans (hcut i.succ).2⟩)
  choose L G f hpieces using hpieces
  exact ⟨n, c, L, G, f, hn, hc, hfirst, hlast, hpieces⟩

end PoincareConjecture
