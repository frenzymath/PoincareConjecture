import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Coordinates
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularLoop

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_exists_local_arc_reparametrization
    {gamma eta : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b p t : ℝ}
    (hinj : InjOn gamma (Icc a b)) (hp : p ∈ Icc a b) (hregular : deriv gamma p ≠ 0)
    (heta : ContDiffAt ℝ ∞ eta t) (hpoint : eta t = gamma p)
    (himage : ∀ᶠ s in 𝓝 t, eta s ∈ gamma '' Icc a b)
    (hetaregular : deriv eta t ≠ 0) :
    ∃ phi : ℝ → ℝ, ContDiffAt ℝ ∞ phi t ∧ phi t = p ∧
      deriv phi t ≠ 0 ∧ eta =ᶠ[𝓝 t] gamma ∘ phi := by
  obtain ⟨l, r, G, L, h, hlp, hpr, hsource, _, _, _,
    _, hGi, _, _, hgraph, _, _, _⟩ :=
    exists_graph_coordinates_of_positive_projection hg (le_refl p)
      (v := deriv gamma p) (by
        intro x hx
        have hx' : x = p := le_antisymm hx.2 hx.1
        subst x
        exact real_inner_self_pos.mpr hregular)
  have hpG : p ∈ G.source := by rw [hsource]; exact ⟨hlp, hpr⟩
  let tail := gamma '' (Icc a b \ G.source)
  have htail : IsClosed tail :=
    ((isCompact_Icc.diff G.open_source).image hg.continuous).isClosed
  have hpTail : eta t ∉ tail := by
    rintro ⟨s, hs, hst⟩
    have hsp : s = p := hinj hs.1 hp (hst.trans hpoint)
    exact hs.2 (hsp ▸ hpG)
  have hpTarget : (L (eta t)).1 ∈ G.target := by
    rw [hpoint, hgraph p hpG]
    exact G.map_source hpG
  let phi : ℝ → ℝ := fun s => G.symm (L (eta s)).1
  have hphi : ContDiffAt ℝ ∞ phi t :=
    (hGi.contDiffAt (G.open_target.mem_nhds hpTarget)).comp t
      ((L.contDiff.contDiffAt.comp t heta).fst)
  have hphip : phi t = p := by
    dsimp only [phi]
    rw [hpoint, hgraph p hpG]
    exact G.left_inv hpG
  have heq : eta =ᶠ[𝓝 t] gamma ∘ phi := by
    filter_upwards [heta.continuousAt.preimage_mem_nhds
      (htail.isOpen_compl.mem_nhds hpTail), himage] with s hs hsi
    obtain ⟨x, hx, hxs⟩ := hsi
    have hxG : x ∈ G.source := by
      by_contra h
      exact hs ⟨x, ⟨hx, h⟩, hxs⟩
    change eta s = gamma (G.symm (L (eta s)).1)
    rw [← hxs, hgraph x hxG, G.left_inv hxG]
  refine ⟨phi, hphi, hphip, ?_, heq⟩
  intro hzero
  have hd := ((hg.differentiable (by simp) (phi t)).hasDerivAt.scomp t
    (hphi.differentiableAt (by simp)).hasDerivAt).deriv
  rw [hzero, zero_smul] at hd
  exact hetaregular (heq.deriv_eq.trans hd)

end PoincareConjecture
