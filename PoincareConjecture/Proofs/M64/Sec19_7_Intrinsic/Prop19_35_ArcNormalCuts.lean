import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopGraphNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Subdivision
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.LinearCoordinates













noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem quarterTurn_coordinates (w : AnnulusCoordinates) :
    quarterTurn w 0 = -w 1 ∧ quarterTurn w 1 = w 0 := by
  simp [quarterTurn_apply, Complex.orthonormalBasisOneI_repr_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]

private theorem projection_quarterTurn
    {v : AnnulusCoordinates} (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hL : ∀ w, L w = (inner ℝ v w, inner ℝ (quarterTurn v) w))
    (w : AnnulusCoordinates) : L (quarterTurn w) = (-(L w).2, (L w).1) := by
  rw [hL, hL]
  have hv := quarterTurn_coordinates v
  have hw := quarterTurn_coordinates w
  ext <;> simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    hv.1, hv.2, hw.1, hw.2]
  ring




theorem m64Intrinsic_graph_tangent
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hf : ContDiffOn ℝ ∞ f G.target)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    {t : ℝ} (ht : t ∈ G.source) :
    L (deriv gamma t) = deriv G t • ((1 : ℝ), deriv f (G t)) := by
  have hdG := (hG.contDiffAt (G.open_source.mem_nhds ht)).differentiableAt (by simp)
  have hdf := (hf.contDiffAt (G.open_target.mem_nhds (G.map_source ht))).differentiableAt
    (by simp)
  have hleft : HasDerivAt (fun s => L (gamma s)) (L (deriv gamma t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t ((hg.differentiable (by simp)) t).hasDerivAt
  have hright := hdG.hasDerivAt.prodMk (hdf.hasDerivAt.comp t hdG.hasDerivAt)
  have heq : (fun s => L (gamma s)) =ᶠ[𝓝 t] fun s => (G s, f (G s)) := by
    filter_upwards [G.open_source.mem_nhds ht] with s hs using hgraph s hs
  have hderiv := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  change L (deriv gamma t) = (deriv G t * 1, deriv G t * deriv f (G t))
  simpa only [mul_one, one_mul, mul_comm] using hderiv




theorem m64Intrinsic_graph_normal_transverse
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {v : AnnulusCoordinates} (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hL : ∀ w, L w = (inner ℝ v w, inner ℝ (quarterTurn v) w))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hf : ContDiffOn ℝ ∞ f G.target)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hpos : 0 < (L (deriv gamma t)).1) :
    0 < (L (quarterTurn (deriv gamma t))).2 -
        deriv f (G t) * (L (quarterTurn (deriv gamma t))).1 ∧
      inner ℝ (deriv gamma t) (quarterTurn (deriv gamma t)) = 0 ∧
      0 < inner ℝ (deriv gamma t) (L.symm (1, deriv f (G t))) := by
  have htan := m64Intrinsic_graph_tangent hg L G hG hf hgraph ht
  have hfirst := congrArg Prod.fst htan
  simp only [Prod.smul_fst, smul_eq_mul, mul_one] at hfirst
  have hd : 0 < deriv G t := hfirst ▸ hpos
  have hregular : deriv gamma t ≠ 0 := by
    intro hzero
    simp [hzero] at hpos
  refine ⟨?_, inner_quarterTurn_self _, ?_⟩
  · rw [projection_quarterTurn L hL, htan]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one]
    nlinarith [mul_nonneg hd.le (sq_nonneg (deriv f (G t)))]
  · have hvector : deriv gamma t = deriv G t • L.symm (1, deriv f (G t)) := by
      apply L.injective
      simpa only [map_smul, L.apply_symm_apply] using htan
    have hinner : inner ℝ (deriv gamma t) (deriv gamma t) =
        deriv G t * inner ℝ (deriv gamma t) (L.symm (1, deriv f (G t))) := by
      conv_lhs => rhs; rw [hvector]
      rw [real_inner_smul_right]
    have hself := real_inner_self_pos.mpr hregular
    exact (mul_pos_iff_of_pos_left hd).mp (hinner ▸ hself)




theorem m64Intrinsic_exists_arc_normal_graph
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) {v : AnnulusCoordinates}
    (hpos : ∀ t ∈ Icc a b, 0 < inner ℝ v (deriv gamma t)) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : OpenPartialHomeomorph ℝ ℝ) (f : ℝ → ℝ),
      Icc a b ⊆ G.source ∧ StrictMonoOn G G.source ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ f G.target ∧
      (∀ t ∈ G.source, L (gamma t) = (G t, f (G t))) ∧
      G '' Icc a b = Icc (G a) (G b) ∧
      Icc (G a) (G b) ⊆ G.target ∧
      (∀ t ∈ Icc a b, 0 < (L (deriv gamma t)).1 ∧
        0 < (L (quarterTurn (deriv gamma t))).2 -
          deriv f (G t) * (L (quarterTurn (deriv gamma t))).1 ∧
        inner ℝ (deriv gamma t) (quarterTurn (deriv gamma t)) = 0 ∧
        0 < inner ℝ (deriv gamma t) (L.symm (1, deriv f (G t)))) ∧
      Nonempty (TransverseGraphCuts f (G a) (G b)
        (L (quarterTurn (deriv gamma a))).1 (L (quarterTurn (deriv gamma a))).2
        (L (quarterTurn (deriv gamma b))).1 (L (quarterTurn (deriv gamma b))).2) := by
  obtain ⟨l, u, G, L, f, hla, hbu, hsource, hGval, hL, hmono, hG,
    _, _, hf, hgraph, himage, htarget, _⟩ :=
    exists_graph_coordinates_of_positive_projection hg hab.le hpos
  have hI : Icc a b ⊆ G.source := by
    rw [hsource]
    exact fun _ ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hbu⟩
  have hmonoG : StrictMonoOn G G.source := by
    intro x hx y hy hxy
    simpa only [hGval] using hmono hx hy hxy
  have htrans (t : ℝ) (ht : t ∈ Icc a b) :
      0 < (L (deriv gamma t)).1 ∧
        0 < (L (quarterTurn (deriv gamma t))).2 -
          deriv f (G t) * (L (quarterTurn (deriv gamma t))).1 ∧
        inner ℝ (deriv gamma t) (quarterTurn (deriv gamma t)) = 0 ∧
        0 < inner ℝ (deriv gamma t) (L.symm (1, deriv f (G t))) := by
    have hp : 0 < (L (deriv gamma t)).1 := by simpa only [hL] using hpos t ht
    exact ⟨hp, m64Intrinsic_graph_normal_transverse hg L hL G hG hf hgraph (hI ht) hp⟩
  refine ⟨L, G, f, hI, hmonoG, hG, hf, hgraph, himage, htarget, htrans, ?_⟩
  have ha := hI (left_mem_Icc.mpr hab.le)
  have hb := hI (right_mem_Icc.mpr hab.le)
  exact exists_transverseGraphCuts G.open_target hf G.open_target hf
    (hmonoG ha hb hab) (G.map_source ha) (G.map_source hb)
    (htrans a (left_mem_Icc.mpr hab.le)).2.1
    (htrans b (right_mem_Icc.mpr hab.le)).2.1




theorem m64Intrinsic_exists_arc_normal_cut_subdivision
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0) :
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
          0 < (L i (deriv gamma t)).1 ∧
          0 < (L i (quarterTurn (deriv gamma t))).2 -
            deriv (f i) (G i t) * (L i (quarterTurn (deriv gamma t))).1 ∧
          inner ℝ (deriv gamma t) (quarterTurn (deriv gamma t)) = 0 ∧
          0 < inner ℝ (deriv gamma t) ((L i).symm (1, deriv (f i) (G i t)))) ∧
        Nonempty (TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
          (L i (quarterTurn (deriv gamma (c i.castSucc)))).1
          (L i (quarterTurn (deriv gamma (c i.castSucc)))).2
          (L i (quarterTurn (deriv gamma (c i.succ)))).1
          (L i (quarterTurn (deriv gamma (c i.succ)))).2) := by
  obtain ⟨n, c, v, hn, hc, hfirst, hlast, hv⟩ :=
    exists_finite_strictMono_projection_subdivision hg hab hregular
  have hpieces (i : Fin n) := m64Intrinsic_exists_arc_normal_graph hg
    (hc Fin.castSucc_lt_succ) (hv i).2.2.1
  choose L G f hpieces using hpieces
  exact ⟨n, c, L, G, f, hn, hc, hfirst, hlast, hpieces⟩

end PoincareConjecture
