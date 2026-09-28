import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularEvolution
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEndCaller

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

theorem exists_stackAnnularMatchedChart
    (T G : OpenPartialHomeomorph P P)
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hG : ContDiffOn ℝ ∞ G G.source) (hGi : ContDiffOn ℝ ∞ G.symm G.target)
    (hTh : ∀ p ∈ T.source, (T p).1 = p.1)
    (hGh : ∀ p ∈ G.source, (G p).1 = p.1)
    (A a b B : ℝ) (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hTs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ T.source)
    (hGs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ G.source)
    (hboundary : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1, T (z, q) = G (z, q)) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 4 ∧
      ∃ Phi : Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞, ∃ S : Set P,
        let Q := Phi.toHomeomorph.toOpenPartialHomeomorph.trans G
        IsCompact S ∧ S ⊆ Ioo A B ×ˢ (univ : Set E2) ∧
        tsupport (fun p : P => Phi p - p) ⊆ S ∧
        tsupport (fun p : P => Phi.symm p - p) ⊆ S ∧
        (∀ p : P, p ∉ S → Phi p = p ∧ Phi.symm p = p) ∧
        (∀ p : P, (Phi p).1 = p.1 ∧ (Phi.symm p).1 = p.1) ∧
        (∀ z : ℝ, ∀ q ∈ sphere (0 : E2) 1,
          Phi (z, q) = (z, q) ∧ Phi.symm (z, q) = (z, q)) ∧
        Q.source = Phi ⁻¹' G.source ∧ Q.target = G.target ∧
        ContDiffOn ℝ ∞ Q Q.source ∧ ContDiffOn ℝ ∞ Q.symm Q.target ∧
        (∀ p ∈ Q.source, (Q p).1 = p.1) ∧
        (∀ p ∈ Q.target, (Q.symm p).1 = p.1) ∧
        (∀ J : Set ℝ,
          Phi '' (J ×ˢ ball (0 : E2) 1) = J ×ˢ ball 0 1 ∧
          Phi '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1 ∧
          Phi.symm '' (J ×ˢ ball (0 : E2) 1) = J ×ˢ ball 0 1 ∧
          Phi.symm '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1 ∧
          Q '' (J ×ˢ ball (0 : E2) 1) = G '' (J ×ˢ ball 0 1) ∧
          Q '' (J ×ˢ closedBall (0 : E2) 1) = G '' (J ×ˢ closedBall 0 1) ∧
          (J ×ˢ closedBall (0 : E2) 1 ⊆ G.source →
            J ×ˢ closedBall (0 : E2) 1 ⊆ Q.source)) ∧
        ∀ z ∈ Icc a b, ∀ x : E2, |‖x‖ - 1| ≤ delta →
          (z, x) ∈ Q.source ∧ Q (z, x) = T (z, x) := by
  have hfiber (V : OpenPartialHomeomorph P P)
      (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
      (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
      (z : ℝ) (hz : ∀ x ∈ closedBall (0 : E2) 1, (z, x) ∈ V.source) :
      ∃ N : BallNeighborhoodChart E2 E2,
        N.chart.source = {x | (z, x) ∈ V.source} ∧
        (∀ x, N.chart x = (V (z, x)).2) ∧
        (∀ y, N.chart.symm y = (V.symm (z, y)).2) := by
    have hVih (p : P) (hp : p ∈ V.target) : (V.symm p).1 = p.1 := by
      have hh := hVh (V.symm p) (V.map_target hp)
      rw [V.right_inv hp] at hh
      exact hh.symm
    have hf : ContDiffOn ℝ ∞ (fun x : E2 => (V (z, x)).2)
        {x | (z, x) ∈ V.source} :=
      (hV.comp (contDiff_prodMk_right z).contDiffOn (fun _ hx => hx)).snd
    have hi : ContDiffOn ℝ ∞ (fun y : E2 => (V.symm (z, y)).2)
        {y | (z, y) ∈ V.target} :=
      (hVi.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd
    have hforward (x : E2) (hx : (z, x) ∈ V.source) :
        (z, (V (z, x)).2) = V (z, x) := Prod.ext (hVh (z, x) hx).symm rfl
    have hinverse (y : E2) (hy : (z, y) ∈ V.target) :
        (z, (V.symm (z, y)).2) = V.symm (z, y) := Prod.ext (hVih (z, y) hy).symm rfl
    let e : OpenPartialHomeomorph E2 E2 := {
      toFun := fun x => (V (z, x)).2
      invFun := fun y => (V.symm (z, y)).2
      source := {x | (z, x) ∈ V.source}
      target := {y | (z, y) ∈ V.target}
      map_source' := by
        intro x hx
        change (z, (V (z, x)).2) ∈ V.target
        rw [hforward x hx]
        exact V.map_source hx
      map_target' := by
        intro y hy
        change (z, (V.symm (z, y)).2) ∈ V.source
        rw [hinverse y hy]
        exact V.map_target hy
      left_inv' := by
        intro x hx
        rw [hforward x hx, V.left_inv hx]
      right_inv' := by
        intro y hy
        rw [hinverse y hy, V.right_inv hy]
      open_source := V.open_source.preimage (continuous_const.prodMk continuous_id)
      open_target := V.open_target.preimage (continuous_const.prodMk continuous_id)
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hi.continuousOn }
    exact ⟨⟨e, hz, hf, hi⟩, rfl, fun _ => rfl, fun _ => rfl⟩
  have hGih (p : P) (hp : p ∈ G.target) : (G.symm p).1 = p.1 := by
    have hh := hGh (G.symm p) (G.map_target hp)
    rw [G.right_inv hp] at hh
    exact hh.symm
  let E := T.trans G.symm
  let g : P → E2 := fun p => (E p).2
  have hEs : ContDiffOn ℝ ∞ E E.source :=
    hGi.comp (hT.mono inter_subset_left) (fun _ hp => hp.2)
  have hEh (p : P) (hp : p ∈ E.source) : (E p).1 = p.1 :=
    (hGih (T p) hp.2).trans (hTh p hp.1)
  have hEsource : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ E.source := by
    intro p hp
    refine ⟨hTs ⟨hp.1, sphere_subset_closedBall hp.2⟩, ?_⟩
    change T p ∈ G.target
    rw [hboundary p.1 hp.1 p.2 hp.2]
    exact G.map_source (hGs ⟨hp.1, sphere_subset_closedBall hp.2⟩)
  have hfixed (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) : g (z, q) = q := by
    change (G.symm (T (z, q))).2 = q
    have hqG : (z, q) ∈ G.source := hGs ⟨hz, sphere_subset_closedBall hq⟩
    exact (congrArg (fun p : P => (G.symm p).2) (hboundary z hz q hq)).trans
      (congrArg Prod.snd (G.left_inv hqG))
  have hnormal (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) :
      0 < ⟪q, fderiv ℝ (fun y => g (z, y)) q q⟫_ℝ := by
    obtain ⟨N, hNs, hNf, _hNi⟩ := hfiber T hT hTi hTh z (fun x hx => hTs ⟨hz, hx⟩)
    obtain ⟨D, _hDs, hDf, hDi⟩ := hfiber G hG hGi hGh z (fun x hx => hGs ⟨hz, hx⟩)
    have hNsource (x : E2) (hx : x ∈ N.chart.source) : (z, x) ∈ T.source := by
      rw [hNs] at hx
      exact hx
    have hcoord (x : E2) (hx : x ∈ N.chart.source) : (z, N.chart x) = T (z, x) :=
      Prod.ext (hTh _ (hNsource x hx)).symm (hNf x)
    have hbound (x : E2) (hx : x ∈ sphere (0 : E2) 1) : N.chart x = D.chart x := by
      rw [hNf, hDf, hboundary z hz x hx]
    have hinside : N.inside = D.inside := N.inside_eq_of_boundary_eq D
      (Module.one_lt_rank_of_one_lt_finrank (by simp [E2])) (image_congr hbound)
    let V := N.chart.trans D.chart.symm
    have hVs : ContDiffOn ℝ ∞ V V.source :=
      D.smooth_symm.comp (N.smooth.mono inter_subset_left) (fun _ hp => hp.2)
    have hVi : ContDiffOn ℝ ∞ V.symm V.target :=
      N.smooth_symm.comp (D.smooth.mono inter_subset_left) (fun _ hp => hp.2)
    have hqN : q ∈ N.chart.source := N.closedBall_subset_source (sphere_subset_closedBall hq)
    have hqD : q ∈ D.chart.source := D.closedBall_subset_source (sphere_subset_closedBall hq)
    have hqV : q ∈ V.source := by
      refine ⟨hqN, ?_⟩
      change N.chart q ∈ D.chart.target
      rw [hbound q hq]
      exact D.chart.map_source hqD
    have hlocal : (fun x => g (z, x)) =ᶠ[𝓝 q] (V : E2 → E2) := by
      filter_upwards [N.chart.open_source.mem_nhds hqN] with x hx
      change (G.symm (T (z, x))).2 = D.chart.symm (N.chart x)
      rw [hDi, hcoord x hx]
    obtain ⟨J, hJ⟩ := exists_smoothChart_derivative V hVs hVi hqV
    have hder : DifferentiableAt ℝ (fun x => g (z, x)) q :=
      hJ.differentiableAt.congr_of_eventuallyEq hlocal
    have hinj : Injective (fderiv ℝ (fun x => g (z, x)) q) := by
      rw [hlocal.fderiv_eq, hJ.fderiv]
      exact J.injective
    apply fderiv_normal_pos_of_local_exterior (fun x => g (z, x))
      (mem_sphere_zero_iff_norm.mp hq) hder
      (Eventually.of_forall (fun x hx => hfixed z hz x (mem_sphere_zero_iff_norm.mpr hx))) hinj
    filter_upwards [V.open_source.mem_nhds hqV, hlocal] with x hx hxe
    intro hxnorm
    rw [hxe]
    by_contra hnot
    have hsmall : V x ∈ ball (0 : E2) 1 := mem_ball_zero_iff.mpr (lt_of_not_ge hnot)
    have hNx : N.chart x ∈ D.inside := ⟨V x, hsmall, D.chart.right_inv hx.2⟩
    rw [← hinside] at hNx
    obtain ⟨v, hv, he⟩ := hNx
    have hvx : v = x := N.chart.injOn
      (N.closedBall_subset_source (ball_subset_closedBall hv)) hx.1 he
    rw [hvx] at hv
    exact (not_lt_of_ge hxnorm) (mem_ball_zero_iff.mp hv)
  obtain ⟨delta, hdelta, hdquarter, e, heq, hes, he, hei, hAnnE, _hinner⟩ :=
    exists_stackAnnularInterpolationChart g E.source E.open_source hEs.snd A a b B
      hAa hab hbB hEsource hfixed hnormal
  obtain ⟨rho, _hrho, _hrhoc, _hrhos, hnear, _hrange, hW, hWc, hWt, hWh, hWq, _hcoords⟩ :=
    exists_stackAnnularCutoff g A a b B delta hAa hab hbB hdelta e heq hes he hei
      (fun z hz q hq => hfixed z ⟨hz.1.le, hz.2.le⟩ q hq)
  obtain ⟨Phi, _H, S, _hSeq, hSc, hSsub, _hPhi, _hPhii, _hPhi0, hPhih,
      hFiber, _hH, _hHi, hCircle, _hDisc, hSupport, hFix, _hTrack, hEndpoint, hProduct⟩ :=
    exists_stackAnnularEvolution g A a b B delta hAa hab hbB hdelta e heq hes he rho
      hnear hW hWc hWt hWh hWq
  let Q := (Phi 1).toHomeomorph.toOpenPartialHomeomorph.trans G
  have hQsource : Q.source = (Phi 1) ⁻¹' G.source := by
    change univ ∩ (Phi 1) ⁻¹' G.source = _
    exact univ_inter _
  have hQtarget : Q.target = G.target := by
    change G.target ∩ G.symm ⁻¹' univ = G.target
    simp only [preimage_univ, inter_univ]
  have hQimage (V : Set P) : Q '' V = G '' ((Phi 1) '' V) := (image_image G (Phi 1) V).symm
  refine ⟨delta, hdelta, hdquarter, Phi 1, S, hSc, hSsub,
    (hSupport 1).1, (hSupport 1).2, hFix 1, hPhih 1, ?_, hQsource, hQtarget, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z q hq
    have hh := (hCircle 1 z q (mem_sphere_zero_iff_norm.mp hq)).1
    exact ⟨hh, by
      simpa only [Diffeomorph.symm_apply_apply] using (congrArg (Phi 1).symm hh).symm⟩
  · exact hG.comp (Phi 1).contDiff.contDiffOn (fun _ hp => hp.2)
  · exact (Phi 1).symm.contDiff.comp_contDiffOn (hGi.mono inter_subset_left)
  · intro p hp
    exact (hGh (Phi 1 p) hp.2).trans (hPhih 1 p).1
  · intro p hp
    exact (hPhih 1 (G.symm p)).2.trans (hGih p hp.1)
  · intro J
    have hh := hProduct 1 J
    refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, ?_, ?_, ?_⟩
    · rw [hQimage, hh.1]
    · rw [hQimage, hh.2.1]
    · intro hJs p hp
      rw [hQsource]
      apply hJs
      exact hh.2.1 ▸ mem_image_of_mem (Phi 1) hp
  · intro z hz x hx
    have hza : z ∈ Ioo A B := ⟨hAa.trans_le hz.1, hz.2.trans_lt hbB⟩
    have hpE : (z, x) ∈ E.source := hAnnE ⟨hza, by
      change |‖x‖ - 1| < 2 * delta
      linarith only [hx, hdelta]⟩
    have hpeq : Phi 1 (z, x) = E (z, x) :=
      Prod.ext ((hPhih 1 (z, x)).1.trans (hEh _ hpE).symm)
        ((hFiber 1 z x).1.symm.trans (hEndpoint z hz x hx))
    refine ⟨?_, ?_⟩
    · rw [hQsource]
      change Phi 1 (z, x) ∈ G.source
      rw [hpeq]
      exact G.map_target hpE.2
    · change G (Phi 1 (z, x)) = T (z, x)
      rw [hpeq]
      exact G.right_inv hpE.2

end PoincareConjecture.M25.Topology3D
