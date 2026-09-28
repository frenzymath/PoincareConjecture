import PoincareConjecture.Proofs.M38.ProjectiveDoubleCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Restriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem exists_ambient_collar_motion
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace StandardCapSpace Q] [T2Space Q]
    (c : PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace Q ∞)
    {δ R : ℝ} (hRδ : R < δ)
    (hc : c.source = univ ×ˢ Ioo (-δ) δ)
    (e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hfix : ∀ s : ℝ, R ≤ |s| → e s = s) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) Q Q ∞,
      (∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-δ) δ →
        H (c (z, s)) = c (z, e s)) ∧
      ∀ x : Q, x ∉ c '' (univ ×ˢ Icc (-R) R) → H x = x := by
  have hcleft {z : RoundCylinderSpace} (hz : z ∈ c.source) : c.symm (c z) = z :=
    c.toPartialEquiv.left_inv hz
  have hcright {x : Q} (hx : x ∈ c.target) : c (c.symm x) = x :=
    c.toPartialEquiv.right_inv hx
  have hinterval (s : ℝ) : e s ∈ Ioo (-δ) δ ↔ s ∈ Ioo (-δ) δ :=
    e.mem_iff_of_fixed_compl
      (S := Ioo (-R) R) (U := Ioo (-δ) δ)
      (fun _ hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun t ht => hfix t (le_of_not_gt (fun h => ht (abs_lt.mp h)))) s
  let d := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr e
  have hpres (z : RoundCylinderSpace) : d z ∈ c.source ↔ z ∈ c.source := by
    rw [hc]
    exact and_congr_right (fun _ => hinterval z.2)
  have hipres {z : RoundCylinderSpace} (hz : z ∈ c.source) : d.symm z ∈ c.source := by
    apply (hpres (d.symm z)).mp
    rwa [d.apply_symm_apply]
  let V : Opens Q := ⟨c.target, c.open_target⟩
  let f : V → V := fun x =>
    ⟨c (d (c.symm x)), c.map_source ((hpres _).mpr (c.map_target x.property))⟩
  let g : V → V := fun x =>
    ⟨c (d.symm (c.symm x)), c.map_source (hipres (c.map_target x.property))⟩
  have hleft (x : V) : g (f x) = x := by
    apply Subtype.ext
    change c (d.symm (c.symm (c (d (c.symm x))))) = x.val
    rw [hcleft (z := d (c.symm x)) ((hpres _).mpr (c.map_target x.property)),
      d.symm_apply_apply, hcright x.property]
  have hright (x : V) : f (g x) = x := by
    apply Subtype.ext
    change c (d (c.symm (c (d.symm (c.symm x))))) = x.val
    rw [hcleft (z := d.symm (c.symm x)) (hipres (c.map_target x.property)),
      d.apply_symm_apply, hcright x.property]
  have hsmooth
      (D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
      (hD : MapsTo D c.source c.source) :
      ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : V => c (D (c.symm x))) := by
    intro x
    have hxs := c.map_target x.property
    have hi := (c.contMDiffOn_invFun.contMDiffAt
      (c.open_target.mem_nhds x.property)).comp x contMDiff_subtype_val.contMDiffAt
    exact (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds (hD hxs))).comp x
      (D.contMDiff.contMDiffAt.comp x hi)
  let F : Diffeomorph (𝓡 3) (𝓡 3) V V ∞ := {
    toFun := f
    invFun := g
    left_inv := hleft
    right_inv := hright
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff V f).mp
      (hsmooth d (fun _ hz => (hpres _).mpr hz))
    contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff V g).mp
      (hsmooth d.symm (fun _ hz => hipres hz)) }
  let K := c '' (univ ×ˢ Icc (-R) R)
  have hstrip : univ ×ˢ Icc (-R) R ⊆ c.source := by
    rw [hc]
    intro z hz
    exact ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hK : IsCompact K :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (c.contMDiffOn_toFun.continuousOn.mono hstrip)
  have hKV : K ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.map_source (hstrip hz)
  have hFfix (x : V) (hx : x.val ∉ K) : F x = x := by
    have hout : R ≤ |(c.symm x).2| := by
      apply le_of_not_gt
      intro ht
      exact hx ⟨c.symm x, ⟨mem_univ _, (abs_le.mp ht.le)⟩,
        c.toPartialEquiv.right_inv x.property⟩
    apply Subtype.ext
    change c ((c.symm x).1, e (c.symm x).2) = x.val
    rw [hfix _ hout, Prod.eta, hcright x.property]
  obtain ⟨H, hH, hHfix⟩ := Diffeomorph.exists_extension_of_isCompact V F hK hKV hFfix
  refine ⟨H, ?_, hHfix⟩
  intro z s hs
  have hzs : (z, s) ∈ c.source := hc.symm ▸ ⟨mem_univ _, hs⟩
  let x : V := ⟨c (z, s), c.map_source hzs⟩
  have h := hH x
  change H (c (z, s)) = c (d (c.symm (c (z, s)))) at h
  rwa [hcleft hzs] at h

end PoincareConjecture.M38
