import PoincareConjecture.Proofs.M38.SphereBundleFlow
import PoincareConjecture.Proofs.M38.SmoothCoverLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

theorem exists_sphereBundle_pullback_cylinder (Q : GeneralizedSliceCarrier)
    [CompactSpace Q.carrier] (B : SurgerySphereBundle Q) :
    let A := circlePullbackCarrier Q B.projection B.projection_smooth
    ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        RoundCylinderSpace A.carrier ∞,
      ∀ p, circlePullbackHeight Q B.projection B.projection_smooth (D p) = p.2 := by
  let A := circlePullbackCarrier Q B.projection B.projection_smooth
  let q := circlePullbackProjection Q B.projection B.projection_smooth
  let h := circlePullbackHeight Q B.projection B.projection_smooth
  have hq := circlePullback_projection_localDiffeomorph Q B.projection B.projection_smooth
  have hh := circlePullback_height_smooth Q B.projection B.projection_smooth
  obtain ⟨U, hU, hbU, f, g, himage, hleft, hright, hf, hg, hproj⟩ :=
    B.local_trivialization (unitCircleExp 0)
  have hginv (p : UnitTwoSphere × UnitCircle) (hp : p ∈ univ ×ˢ U) :
      B.projection (g p) = p.2 := by
    obtain ⟨y, hy, hfy⟩ := himage.symm ▸ hp
    rw [← hfy, hleft hy, hproj y hy]
  let S : UnitTwoSphere → A.carrier := fun z =>
    ⟨(g (z, unitCircleExp 0), 0), hginv _ ⟨mem_univ _, hbU⟩⟩
  have hSheight (z : UnitTwoSphere) : h (S z) = 0 := rfl
  have hSbase : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun z : UnitTwoSphere => g (z, unitCircleExp 0)) := by
    apply contMDiffOn_univ.mp
    exact hg.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun _ _ => ⟨mem_univ _, hbU⟩)
  have hScont : Continuous S :=
    (hSbase.continuous.prodMk continuous_const).subtype_mk _
  have hS : ContMDiff (𝓡 2) (𝓡 3) ∞ S :=
    continuous_lift_smooth (𝓡 2) q hq S hScont hSbase
  let R : A.carrier → UnitTwoSphere := fun a => (f (q a)).1
  have hRS (z : UnitTwoSphere) : R (S z) = z :=
    congrArg Prod.fst (hright (show (z, unitCircleExp 0) ∈ univ ×ˢ U from
      ⟨mem_univ _, hbU⟩))
  have hlevel (a : A.carrier) (ha : h a = 0) : B.projection (q a) = unitCircleExp 0 := by
    have he : B.projection (q a) = unitCircleExp (h a) :=
      CirclePullback.projection_height B.projection a
    rwa [ha] at he
  have hSR (a : A.carrier) (ha : h a = 0) : S (R a) = a := by
    have hau : q a ∈ B.projection ⁻¹' U := by
      change B.projection (q a) ∈ U
      rw [hlevel a ha]
      exact hbU
    have he : ((f (q a)).1, unitCircleExp 0) = f (q a) :=
      Prod.ext rfl ((hlevel a ha).symm.trans (hproj (q a) hau).symm)
    apply Subtype.ext
    apply Prod.ext
    · change g ((f (q a)).1, unitCircleExp 0) = q a
      rw [he, hleft hau]
    · exact ha.symm
  obtain ⟨Φ, hi, hadd, hΦ, hclock⟩ := exists_sphereBundle_pullback_flow Q B
  change ∀ t a, h (Φ t a) = h a + t at hclock
  let Z : A.carrier → A.carrier := fun a => Φ (-h a) a
  have hZ : ContMDiff (𝓡 3) (𝓡 3) ∞ Z :=
    hΦ.comp (hh.neg.prodMk contMDiff_id)
  have hZzero (a : A.carrier) : h (Z a) = 0 := by
    change h (Φ (-h a) a) = 0
    rw [hclock]
    exact add_neg_cancel _
  have hRZ : ContMDiff (𝓡 3) (𝓡 2) ∞ (R ∘ Z) := by
    have hs : ContMDiff (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞
        (fun a => f (q (Z a))) := by
      apply contMDiffOn_univ.mp
      apply hf.comp (hq.contMDiff.comp hZ).contMDiffOn
      intro a _
      change B.projection (q (Z a)) ∈ U
      rw [hlevel (Z a) (hZzero a)]
      exact hbU
    exact hs.fst
  let D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace A.carrier ∞ := {
    toEquiv := {
      toFun := fun p => Φ p.2 (S p.1)
      invFun := fun a => (R (Z a), h a)
      left_inv := by
        intro p
        have hc : h (Φ p.2 (S p.1)) = p.2 := by
          rw [hclock, hSheight, zero_add]
        have hz : Z (Φ p.2 (S p.1)) = S p.1 := by
          change Φ (-h (Φ p.2 (S p.1))) (Φ p.2 (S p.1)) = S p.1
          rw [hc, ← hadd, neg_add_cancel, hi]
        exact Prod.ext (by change R (Z (Φ p.2 (S p.1))) = p.1; rw [hz, hRS]) hc
      right_inv := by
        intro a
        change Φ (h a) (S (R (Z a))) = a
        rw [hSR (Z a) (hZzero a)]
        change Φ (h a) (Φ (-h a) a) = a
        rw [← hadd, add_neg_cancel, hi] }
    contMDiff_toFun := hΦ.comp (contMDiff_snd.prodMk (hS.comp contMDiff_fst))
    contMDiff_invFun := hRZ.prodMk hh }
  refine ⟨D, fun p => ?_⟩
  change h (Φ p.2 (S p.1)) = p.2
  rw [hclock, hSheight, zero_add]

end PoincareConjecture.M38
