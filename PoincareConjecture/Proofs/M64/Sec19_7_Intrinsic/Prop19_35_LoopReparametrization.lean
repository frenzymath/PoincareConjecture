import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopGraphNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_exists_local_loop_reparametrization
    {gamma eta : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p t : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    (heta : ContDiffAt ℝ ∞ eta t) (hpoint : eta t = gamma p)
    (himage : ∀ᶠ s in 𝓝 t, eta s ∈ gamma '' Icc 0 T)
    (hetaregular : deriv eta t ≠ 0) :
    ∃ phi : ℝ → ℝ, ContDiffAt ℝ ∞ phi t ∧ phi t = p ∧
      deriv phi t ≠ 0 ∧ eta =ᶠ[𝓝 t] gamma ∘ phi := by
  obtain ⟨l, r, G, L, h, hlp, hpr, hsource, hG, hL, hmono,
    _, hGi, _, hh, hgraph, _, _, _⟩ :=
    exists_graph_coordinates_of_positive_projection hg (le_refl p)
      (v := deriv gamma p) (by
        intro x hx
        have hx' : x = p := le_antisymm hx.2 hx.1
        subst x
        exact real_inner_self_pos.mpr hregular)
  have hmonoG : StrictMonoOn G G.source := by
    intro x hx y hy hxy
    simpa only [hG] using hmono hx hy hxy
  obtain ⟨W, hW, harc, hWgraph⟩ := m64Intrinsic_loop_graph_neighborhood hg.continuous
    hend hinj L G h (le_refl p) hp.1 hp.2 hlp hpr hsource hmonoG hgraph
  have hpW : eta t ∈ W := by
    rw [hpoint]
    exact harc ⟨p, ⟨le_rfl, le_rfl⟩, rfl⟩
  let phi : ℝ → ℝ := fun s => G.symm (L (eta s)).1
  have hphi : ContDiffAt ℝ ∞ phi t :=
    (hGi.contDiffAt (G.open_target.mem_nhds (hWgraph _ hpW).1)).comp t
      ((L.contDiff.contDiffAt.comp t heta).fst)
  have hpG : p ∈ G.source := by rw [hsource]; exact ⟨hlp, hpr⟩
  have hphip : phi t = p := by
    dsimp only [phi]
    rw [hpoint, hgraph p hpG]
    exact G.left_inv hpG
  have heq : eta =ᶠ[𝓝 t] gamma ∘ phi := by
    filter_upwards [heta.continuousAt.preimage_mem_nhds (hW.mem_nhds hpW), himage] with s hs hsi
    have htarget := (hWgraph _ hs).1
    have hgraphEta := (hWgraph _ hs).2.mp hsi
    apply L.injective
    change L (eta s) = L (gamma (G.symm (L (eta s)).1))
    rw [hgraph _ (G.map_target htarget), G.right_inv htarget]
    exact Prod.ext rfl hgraphEta
  refine ⟨phi, hphi, hphip, ?_, heq⟩
  intro hzero
  have hd := ((hg.differentiable (by simp) (phi t)).hasDerivAt.scomp t
    (hphi.differentiableAt (by simp)).hasDerivAt).deriv
  rw [hzero, zero_smul] at hd
  exact hetaregular (heq.deriv_eq.trans hd)

end PoincareConjecture
