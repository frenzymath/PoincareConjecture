import PoincareConjecture.Proofs.M64.Mathlib.ContinuousGraphShear
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopRegionChart










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_continuous_graph_defining_function
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    {h : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hh : ContinuousOn h X)
    {p : AnnulusCoordinates} {d : ℝ} (hdh : HasDerivAt h d (L p).1)
    {U V W : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfV : frontier V = frontier U)
    (hW : IsOpen W) (hpW : p ∈ W) (hpfront : p ∈ frontier U)
    (hgraph : ∀ z ∈ W, (L z).1 ∈ X ∧ (z ∈ frontier U ↔ (L z).2 = h (L z).1)) :
    ∃ (phi : AnnulusCoordinates → ℝ) (ell : AnnulusCoordinates →L[ℝ] ℝ),
      HasFDerivAt phi ell p ∧ phi p = 0 ∧ ell ≠ 0 ∧
        (∀ᶠ z in 𝓝 p, z ∈ closure U ↔ 0 ≤ phi z) := by
  let H := (m64ContinuousGraphShear hX hh).trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsource : H.source = X ×ˢ univ := by
    ext q
    simp [H, m64ContinuousGraphShear]
  have hformula (q : ℝ × ℝ) : H q = L.symm (q.1, h q.1 + q.2) := rfl
  let x := (L p).1
  have hxX : x ∈ X := (hgraph p hpW).1
  have hpgraph : (L p).2 = h x := (hgraph p hpW).2.mp hpfront
  have hcoord : L p = (x, h x) := Prod.ext rfl hpgraph
  have hx : (x, (0 : ℝ)) ∈ H.source := by rw [hsource]; exact ⟨hxX, mem_univ _⟩
  have hbase : H (x, 0) = p := by rw [hformula, add_zero, ← hcoord, L.symm_apply_apply]
  have hpre : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ W :=
    (H.continuousAt hx).preimage_mem_nhds (by simpa only [hbase] using hW.mem_nhds hpW)
  have hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0 := by
    filter_upwards [hpre] with z hz
    rw [(hgraph (H z) hz).2, hformula, L.apply_symm_apply]
    simp only [add_eq_left]
  have hside := m64Intrinsic_jordan_product_line_germ hU hV hdisj hfV.symm H hx
    (by rw [hbase]; exact hpfront) hline
  let X0 : AnnulusCoordinates →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let Y0 : AnnulusCoordinates →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let phi := fun z => Y0 z - h (X0 z)
  let ell : AnnulusCoordinates →L[ℝ] ℝ := Y0 - d • X0
  have hd : HasFDerivAt phi ell p :=
    Y0.hasFDerivAt.sub (hdh.comp_hasFDerivAt_of_eq p X0.hasFDerivAt rfl)
  have hzero : phi p = 0 := sub_eq_zero.mpr hpgraph
  have hv : ell (L.symm (0, 1)) = 1 := by
    change (L (L.symm (0, 1))).2 - d * (L (L.symm (0, 1))).1 = 1
    rw [L.apply_symm_apply]
    simp
  have hell : ell ≠ 0 := by
    intro heq
    have hz : ell (L.symm (0, 1)) = 0 := by rw [heq]; rfl
    linarith
  let psi := fun z : AnnulusCoordinates => ((L z).1, (L z).2 - h (L z).1)
  have hshift : ContinuousAt psi p :=
    L.continuous.fst.continuousAt.prodMk (L.continuous.snd.continuousAt.sub
      (hdh.continuousAt.comp_of_eq L.continuous.fst.continuousAt rfl))
  have ht : Tendsto psi (𝓝 p) (𝓝 (x, (0 : ℝ))) := by
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
