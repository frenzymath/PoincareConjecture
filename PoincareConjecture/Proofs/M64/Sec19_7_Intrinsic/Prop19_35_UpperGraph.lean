import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopRegionChart

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_upper_graph
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ) (X : Set ℝ) (x : ℝ),
      IsOpen X ∧ x ∈ X ∧ ContDiffOn ℝ ∞ h X ∧ L (gamma p) = (x, h x) ∧
      ∀ᶠ z in 𝓝 (x, h x),
        (L.symm z ∈ closure U ↔ h z.1 ≤ z.2) ∧
          (L.symm z ∈ frontier U ↔ z.2 = h z.1) := by
  obtain ⟨L, h, X, W, hX, hh, hW, hpW, hWgraph⟩ :=
    m64Intrinsic_exists_regular_loop_graph_neighborhood hg hend hinj hp hregular
  obtain ⟨H, hsource, _, hformula, _, _⟩ := m64Intrinsic_graph_straightening_chart L hX hh
  let x := (L (gamma p)).1
  have hxX : x ∈ X := (hWgraph (gamma p) hpW).1
  have hpgraph : (L (gamma p)).2 = h x :=
    (hWgraph (gamma p) hpW).2.mp ⟨p, ⟨hp.1.le, hp.2.le⟩, rfl⟩
  have hcoord : L (gamma p) = (x, h x) := Prod.ext rfl hpgraph
  have hbase : L.symm (x, h x) = gamma p := by rw [← hcoord, L.symm_apply_apply]
  have hx : (x, 0) ∈ H.source := by rw [hsource]; exact ⟨hxX, mem_univ _⟩
  have hHbase : H (x, 0) = gamma p := by rw [hformula, add_zero, hbase]
  have hfront : H (x, 0) ∈ frontier U := by
    rw [hHbase, hfU]
    exact ⟨p, ⟨hp.1.le, hp.2.le⟩, rfl⟩
  have hpre : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ W :=
    (H.continuousAt hx).preimage_mem_nhds (by simpa only [hHbase] using hW.mem_nhds hpW)
  have hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0 := by
    filter_upwards [hpre] with z hz
    rw [hfU, (hWgraph (H z) hz).2, hformula, L.apply_symm_apply]
    simp only [add_eq_left]
  have hside := m64Intrinsic_jordan_product_line_germ hU hV hdisj
    (hfU.trans hfV.symm) H hx hfront hline
  have hhx : ContinuousAt h x :=
    (hh x hxX).continuousWithinAt.continuousAt (hX.mem_nhds hxX)
  have hshift : ContinuousAt (fun z : ℝ × ℝ => (z.1, z.2 - h z.1)) (x, h x) :=
    continuousAt_fst.prodMk (continuousAt_snd.sub (hhx.comp continuousAt_fst))
  have hgraph : ∀ᶠ z in 𝓝 (x, h x), L.symm z ∈ frontier U ↔ z.2 = h z.1 := by
    have hw := L.symm.continuous.continuousAt.preimage_mem_nhds
      (show W ∈ 𝓝 (L.symm (x, h x)) by rw [hbase]; exact hW.mem_nhds hpW)
    filter_upwards [hw] with z hz
    rw [hfU, (hWgraph (L.symm z) hz).2, L.apply_symm_apply]
  rcases hside with hside | hside
  · have hs := hshift.eventually (by simpa only [sub_self] using hside)
    refine ⟨L, h, X, x, hX, hxX, hh, hcoord, ?_⟩
    filter_upwards [hs, hgraph] with z hz hzg
    rw [hformula, add_sub_cancel] at hz
    exact ⟨hz.trans sub_nonneg, hzg⟩
  · have hs := hshift.eventually (by simpa only [sub_self] using hside)
    have hdown : ∀ᶠ z in 𝓝 (x, h x),
        (L.symm z ∈ closure U ↔ z.2 ≤ h z.1) ∧
          (L.symm z ∈ frontier U ↔ z.2 = h z.1) := by
      filter_upwards [hs, hgraph] with z hz hzg
      rw [hformula, add_sub_cancel] at hz
      exact ⟨hz.trans sub_nonpos, hzg⟩
    let E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
      (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)
    let K := L.trans E
    have hK (z : ℝ × ℝ) : K.symm z = L.symm (z.1, -z.2) := rfl
    have he : E (x, h x) = (x, -h x) := rfl
    have he' : E.symm (x, -h x) = (x, h x) := by
      change (x, - -h x) = (x, h x)
      rw [neg_neg]
    refine ⟨K, fun s => -h s, X, x, hX, hxX, hh.neg, ?_, ?_⟩
    · change E (L (gamma p)) = (x, -h x)
      rw [hcoord, he]
    · have hs' := E.symm.continuous.continuousAt.eventually
        (show ∀ᶠ z in 𝓝 (E.symm (x, -h x)),
          (L.symm z ∈ closure U ↔ z.2 ≤ h z.1) ∧
            (L.symm z ∈ frontier U ↔ z.2 = h z.1) by rw [he']; exact hdown)
      filter_upwards [hs'] with z hz
      change (L.symm (z.1, -z.2) ∈ closure U ↔ -z.2 ≤ h z.1) ∧
        (L.symm (z.1, -z.2) ∈ frontier U ↔ -z.2 = h z.1) at hz
      rw [hK]
      exact ⟨hz.1.trans (by constructor <;> intro h' <;> linarith),
        hz.2.trans (by constructor <;> intro h' <;> linarith)⟩

end PoincareConjecture
