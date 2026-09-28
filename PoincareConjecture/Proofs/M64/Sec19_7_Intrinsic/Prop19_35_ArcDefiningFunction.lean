import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcGraphNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopRegionChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_exists_arc_defining_function
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b p : ℝ}
    (hinj : InjOn gamma (Icc a b)) (hp : p ∈ Ioo a b) (hregular : deriv gamma p ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc a b ∪ K) (hfV : frontier V = frontier U) :
    ∃ (phi : AnnulusCoordinates → ℝ) (ell : AnnulusCoordinates →L[ℝ] ℝ),
      HasFDerivAt phi ell (gamma p) ∧ phi (gamma p) = 0 ∧ ell ≠ 0 ∧
        (∀ᶠ z in 𝓝 (gamma p), z ∈ closure U ↔ 0 ≤ phi z) := by
  obtain ⟨L, h, X, W, hX, hh, hW, hpW, hWgraph⟩ :=
    m64Intrinsic_exists_arc_graph_neighborhood hg hinj hp hregular hK hpK
  obtain ⟨H, hsource, _, hformula, _, _⟩ := m64Intrinsic_graph_straightening_chart L hX hh
  let x := (L (gamma p)).1
  have hxX : x ∈ X := (hWgraph (gamma p) hpW).1
  have hpgraph : (L (gamma p)).2 = h x :=
    (hWgraph (gamma p) hpW).2.mp (Or.inl ⟨p, Ioo_subset_Icc_self hp, rfl⟩)
  have hcoord : L (gamma p) = (x, h x) := Prod.ext rfl hpgraph
  have hbase : L.symm (x, h x) = gamma p := by rw [← hcoord, L.symm_apply_apply]
  have hx : (x, 0) ∈ H.source := by rw [hsource]; exact ⟨hxX, mem_univ _⟩
  have hHbase : H (x, 0) = gamma p := by rw [hformula, add_zero, hbase]
  have hfront : H (x, 0) ∈ frontier U := by
    rw [hHbase, hfU]
    exact Or.inl ⟨p, Ioo_subset_Icc_self hp, rfl⟩
  have hpre : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ W :=
    (H.continuousAt hx).preimage_mem_nhds (by simpa only [hHbase] using hW.mem_nhds hpW)
  have hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0 := by
    filter_upwards [hpre] with z hz
    rw [hfU, (hWgraph (H z) hz).2, hformula, L.apply_symm_apply]
    simp only [add_eq_left]
  have hside := m64Intrinsic_jordan_product_line_germ hU hV hdisj hfV.symm H hx hfront hline
  let X0 : AnnulusCoordinates →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let Y0 : AnnulusCoordinates →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let phi := fun z => Y0 z - h (X0 z)
  let ell : AnnulusCoordinates →L[ℝ] ℝ := Y0 - deriv h x • X0
  have hdh : HasDerivAt h (deriv h x) x :=
    ((hh x hxX).contDiffAt (hX.mem_nhds hxX)).differentiableAt (by simp) |>.hasDerivAt
  have hXbase : X0 (gamma p) = x := rfl
  have hYbase : Y0 (gamma p) = h x := hpgraph
  have hd : HasFDerivAt phi ell (gamma p) :=
    Y0.hasFDerivAt.sub (hdh.comp_hasFDerivAt_of_eq (gamma p) X0.hasFDerivAt hXbase.symm)
  have hzero : phi (gamma p) = 0 := by simp only [phi, hXbase, hYbase, sub_self]
  have hv : ell (L.symm (0, 1)) = 1 := by
    change (L (L.symm (0, 1))).2 - deriv h x * (L (L.symm (0, 1))).1 = 1
    rw [L.apply_symm_apply]
    simp
  have hell : ell ≠ 0 := by
    intro heq
    have hz : ell (L.symm (0, 1)) = 0 := by rw [heq]; rfl
    linarith
  let psi := fun z : AnnulusCoordinates => ((L z).1, (L z).2 - h (L z).1)
  have hshift : ContinuousAt psi (gamma p) :=
    L.continuous.fst.continuousAt.prodMk (L.continuous.snd.continuousAt.sub
      (hdh.continuousAt.comp_of_eq L.continuous.fst.continuousAt rfl))
  have ht : Tendsto psi (𝓝 (gamma p)) (𝓝 (x, (0 : ℝ))) := by
    simpa only [psi, hcoord, sub_self] using hshift.tendsto
  have hcancel (z : AnnulusCoordinates) : H (psi z) = z := by
    rw [hformula]
    simp only [psi, add_sub_cancel, L.symm_apply_apply]
  rcases hside with hs | hs
  · refine ⟨phi, ell, hd, hzero, hell, ?_⟩
    filter_upwards [ht.eventually hs] with z hz
    rw [hcancel] at hz
    exact hz
  · refine ⟨fun z => -phi z, -ell, hd.neg, by simp only [hzero, neg_zero],
      neg_ne_zero.mpr hell, ?_⟩
    filter_upwards [ht.eventually hs] with z hz
    rw [hcancel] at hz
    exact hz.trans neg_nonneg.symm

end PoincareConjecture
