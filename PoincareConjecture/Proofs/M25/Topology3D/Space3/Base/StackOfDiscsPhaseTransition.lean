import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsRadialPhase
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalSign

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem stackHeightChart_normal_pos
    (Q : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hQ : ContDiffOn ℝ ∞ Q Q.source)
    (hQi : ContDiffOn ℝ ∞ Q.symm Q.target)
    (hQh : ∀ p ∈ Q.source, (Q p).1 = p.1)
    (z : ℝ) (q : E2) (hq : ‖q‖ = 1) (hs : (z, q) ∈ Q.source)
    (hfixed : ∀ x : E2, ‖x‖ = 1 → (Q (z, x)).2 = x)
    (hout : ∀ x : E2, (z, x) ∈ Q.source →
      1 ≤ ‖x‖ → 1 ≤ ‖(Q (z, x)).2‖) :
    0 < ⟪q, fderiv ℝ (fun x => (Q (z, x)).2) q q⟫_ℝ := by
  have hQih (p : ℝ × E2) (hp : p ∈ Q.target) : (Q.symm p).1 = p.1 := by
    have hh := hQh (Q.symm p) (Q.map_target hp)
    rw [Q.right_inv hp] at hh
    exact hh.symm
  have hf : ContDiffOn ℝ ∞ (fun x : E2 => (Q (z, x)).2)
      {x | (z, x) ∈ Q.source} :=
    (hQ.comp (contDiff_prodMk_right z).contDiffOn (fun _ hx => hx)).snd
  have hi : ContDiffOn ℝ ∞ (fun y : E2 => (Q.symm (z, y)).2)
      {y | (z, y) ∈ Q.target} :=
    (hQi.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd
  have hforward (x : E2) (hx : (z, x) ∈ Q.source) :
      (z, (Q (z, x)).2) = Q (z, x) := Prod.ext (hQh (z, x) hx).symm rfl
  have hinverse (y : E2) (hy : (z, y) ∈ Q.target) :
      (z, (Q.symm (z, y)).2) = Q.symm (z, y) := Prod.ext (hQih (z, y) hy).symm rfl
  let V : OpenPartialHomeomorph E2 E2 := {
    toFun := fun x => (Q (z, x)).2
    invFun := fun y => (Q.symm (z, y)).2
    source := {x | (z, x) ∈ Q.source}
    target := {y | (z, y) ∈ Q.target}
    map_source' := by
      intro x hx
      change (z, (Q (z, x)).2) ∈ Q.target
      rw [hforward x hx]
      exact Q.map_source hx
    map_target' := by
      intro y hy
      change (z, (Q.symm (z, y)).2) ∈ Q.source
      rw [hinverse y hy]
      exact Q.map_target hy
    left_inv' := by
      intro x hx
      rw [hforward x hx, Q.left_inv hx]
    right_inv' := by
      intro y hy
      rw [hinverse y hy, Q.right_inv hy]
    open_source := Q.open_source.preimage (continuous_const.prodMk continuous_id)
    open_target := Q.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hi.continuousOn }
  obtain ⟨J, hJ⟩ := exists_smoothChart_derivative V hf hi hs
  have hd : HasFDerivAt (fun x => (Q (z, x)).2) (J : E2 →L[ℝ] E2) q := hJ
  apply fderiv_normal_pos_of_local_exterior (fun x => (Q (z, x)).2)
    hq hd.differentiableAt (Eventually.of_forall hfixed)
  · rw [hd.fderiv]
    exact J.injective
  · filter_upwards [V.open_source.mem_nhds hs] with x hx
    exact hout x hx

theorem stackCirclePhaseTransition_spec
    (E R : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hE : ContDiffOn ℝ ∞ E E.source)
    (hEi : ContDiffOn ℝ ∞ E.symm E.target)
    (hEh : ∀ p ∈ E.source, (E p).1 = p.1)
    (hEs : univ ×ˢ sphere (0 : E2) 1 ⊆ E.source)
    (hEiB : MapsTo E.symm (univ ×ˢ ball (0 : E2) 1)
      (univ ×ˢ ball (0 : E2) 1))
    (hR : ContDiffOn ℝ ∞ R R.source)
    (hRi : ContDiffOn ℝ ∞ R.symm R.target)
    (hRs : R.source = univ ×ˢ ({0}ᶜ : Set E2))
    (hRh : ∀ p, (R p).1 = p.1 ∧ (R.symm p).1 = p.1)
    (hRn : ∀ p, ‖(R p).2‖ = ‖p.2‖ ∧ ‖(R.symm p).2‖ = ‖p.2‖)
    (hboundary : ∀ p ∈ univ ×ˢ sphere (0 : E2) 1, R p = E p) :
    let Q := E.trans R.symm
    Q.source = E.source ∩ E ⁻¹' R.target ∧
    Q.target = R.source ∩ R ⁻¹' E.target ∧
    ContDiffOn ℝ ∞ Q Q.source ∧
    ContDiffOn ℝ ∞ Q.symm Q.target ∧
    (∀ p ∈ Q.source, (Q p).1 = p.1) ∧
    (univ ×ˢ sphere (0 : E2) 1 ⊆ Q.source) ∧
    (∀ p ∈ univ ×ˢ sphere (0 : E2) 1, Q p = p) ∧
    ∀ z : ℝ, ∀ q : E2, ‖q‖ = 1 →
      0 < ⟪q, fderiv ℝ (fun x => (Q (z, x)).2) q q⟫_ℝ := by
  dsimp only
  let Q := E.trans R.symm
  have hQs : ContDiffOn ℝ ∞ Q Q.source :=
    hRi.comp (hE.mono inter_subset_left) (fun _ hp => hp.2)
  have hQsi : ContDiffOn ℝ ∞ Q.symm Q.target :=
    hEi.comp (hR.mono inter_subset_left) (fun _ hp => hp.2)
  have hQh (p : ℝ × E2) (hp : p ∈ Q.source) : (Q p).1 = p.1 :=
    ((hRh (E p)).2).trans (hEh p hp.1)
  have hRC (p : ℝ × E2) (hp : p ∈ univ ×ˢ sphere (0 : E2) 1) : p ∈ R.source := by
    rw [hRs]
    exact ⟨mem_univ _, ne_zero_of_mem_unit_sphere ⟨p.2, hp.2⟩⟩
  have hQC : univ ×ˢ sphere (0 : E2) 1 ⊆ Q.source := by
    intro p hp
    refine ⟨hEs hp, ?_⟩
    change E p ∈ R.target
    rw [← hboundary p hp]
    exact R.map_source (hRC p hp)
  have hfixed (p : ℝ × E2) (hp : p ∈ univ ×ˢ sphere (0 : E2) 1) : Q p = p := by
    change R.symm (E p) = p
    rw [← hboundary p hp]
    exact R.left_inv (hRC p hp)
  refine ⟨rfl, rfl, hQs, hQsi, hQh, hQC, hfixed, ?_⟩
  intro z q hq
  have hqC : (z, q) ∈ univ ×ˢ sphere (0 : E2) 1 :=
    ⟨mem_univ _, mem_sphere_zero_iff_norm.mpr hq⟩
  apply stackHeightChart_normal_pos Q hQs hQsi hQh z q hq (hQC hqC)
  · intro x hx
    exact congrArg Prod.snd (hfixed (z, x) ⟨mem_univ _, mem_sphere_zero_iff_norm.mpr hx⟩)
  · intro x hx hxnorm
    change 1 ≤ ‖(R.symm (E (z, x))).2‖
    rw [(hRn (E (z, x))).2]
    by_contra hnot
    have hsmall : E (z, x) ∈ univ ×ˢ ball (0 : E2) 1 :=
      ⟨mem_univ _, mem_ball_zero_iff.mpr (lt_of_not_ge hnot)⟩
    have hxsmall := (hEiB hsmall).2
    rw [E.left_inv hx.1] at hxsmall
    exact (not_lt_of_ge hxnorm) (mem_ball_zero_iff.mp hxsmall)

end PoincareConjecture.M25.Topology3D
