import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCollar
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SphereGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology IsManifold
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem threeSphereStereographic_isLocalDiffeomorphOn (p0 : UnitThreeSphere) :
    IsLocalDiffeomorphOn (𝓡 3) 𝓘(ℝ, E3) ∞ (threeSphereStereographic p0)
      (threeSphereStereographic p0).source := by
  let e := threeSphereStereographic p0
  have he := threeSphereStereographic_mem_maximalAtlas p0
  let d : PartialDiffeomorph (𝓡 3) 𝓘(ℝ, E3) UnitThreeSphere E3 ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  intro x
  exact ⟨d, x.2, fun _ _ => rfl⟩

theorem projective_collar_stereographic_control
    {p : RealProjectiveThree} (p0 : UnitThreeSphere) (hp0 : Quotient.mk' p0 = p)
    {a b : ℝ} {L : UnitTwoSphere × ℝ → UnitThreeSphere}
    (hD : MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      L (univ ×ˢ Ioo a b))
    (hinj : InjOn L (univ ×ˢ Ioo a b)) :
    MapsTo L (univ ×ˢ Ioo a b) (threeSphereStereographic p0).source ∧
    EqOn ((threeSphereStereographic p0).symm ∘ threeSphereStereographic p0 ∘ L)
      L (univ ×ˢ Ioo a b) ∧
    MapsTo (threeSphereStereographic p0 ∘ L) (univ ×ˢ Ioo a b) ({0} : Set E3)ᶜ ∧
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
      (threeSphereStereographic p0 ∘ L) (univ ×ˢ Ioo a b) ∧
    InjOn (threeSphereStereographic p0 ∘ L) (univ ×ˢ Ioo a b) := by
  have hpair (z : UnitTwoSphere × ℝ) (hz : z ∈ univ ×ˢ Ioo a b) :
      L z ∈ ({p0, -p0} : Set UnitThreeSphere)ᶜ := by
    rw [← projectiveCoverDomain_eq_compl_pair p0 hp0]
    exact hD hz
  have hsource : MapsTo L (univ ×ˢ Ioo a b) (threeSphereStereographic p0).source := by
    intro z hz
    rw [threeSphereStereographic_source]
    change L z ≠ p0
    intro heq
    exact hpair z hz (by simp [heq])
  refine ⟨hsource, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (threeSphereStereographic p0).left_inv (hsource hz)
  · intro z hz
    change threeSphereStereographic p0 (L z) ≠ 0
    intro hzero
    have hanti : L z = -p0 := by
      calc
        L z = (threeSphereStereographic p0).symm
            (threeSphereStereographic p0 (L z)) :=
          ((threeSphereStereographic p0).left_inv (hsource hz)).symm
        _ = (threeSphereStereographic p0).symm 0 := congrArg _ hzero
        _ = -p0 := threeSphereStereographic_symm_zero p0
    exact hpair z hz (by simp [hanti])
  · intro z
    exact (hloc z).comp 𝓘(ℝ, E3) E3
      (threeSphereStereographic_isLocalDiffeomorphOn p0 ⟨L z.1, hsource z.2⟩)
  · intro z hz w hw heq
    exact hinj hz hw ((threeSphereStereographic p0).injOn (hsource hz) (hsource hw) heq)

theorem projective_collar_stereographic_disjoint
    {p : RealProjectiveThree} (p0 : UnitThreeSphere) (hp0 : Quotient.mk' p0 = p)
    {a b : ℝ} {L1 L2 : UnitTwoSphere × ℝ → UnitThreeSphere}
    (hD1 : MapsTo L1 (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hD2 : MapsTo L2 (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hd : Disjoint (L1 '' (univ ×ˢ Ioo a b)) (L2 '' (univ ×ˢ Ioo a b))) :
    Disjoint ((threeSphereStereographic p0 ∘ L1) '' (univ ×ˢ Ioo a b))
      ((threeSphereStereographic p0 ∘ L2) '' (univ ×ˢ Ioo a b)) := by
  have hsource {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain p) :
      x ∈ (threeSphereStereographic p0).source := by
    rw [threeSphereStereographic_source]
    change x ≠ p0
    intro heq
    subst x
    exact hx hp0
  rw [Set.disjoint_left] at hd ⊢
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
  have hvalues : L1 z = L2 w := (threeSphereStereographic p0).injOn
    (hsource (hD1 hz)) (hsource (hD2 hw)) heq.symm
  exact hd ⟨z, hz, rfl⟩ ⟨w, hw, hvalues.symm⟩

theorem projective_collar_stereographic_normalized
    {p : RealProjectiveThree} (p0 : UnitThreeSphere) (hp0 : Quotient.mk' p0 = p)
    {a b : ℝ} {L : UnitTwoSphere × ℝ → UnitThreeSphere}
    (hD : MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      L (univ ×ˢ Ioo a b))
    (hinj : InjOn L (univ ×ˢ Ioo a b))
    (t0 rho : ℝ) (hrho : 0 < rho) (ha : a < t0 - rho) (hb : t0 + rho < b) :
    let Psi := fun z : UnitTwoSphere × ℝ =>
      threeSphereStereographic p0 (L (z.1, t0 + rho * z.2))
    IsCollarEmbedding Psi ∧
    IsClosedEmbedding (fun z : UnitTwoSphere × Icc (-1 : ℝ) 1 => Psi (z.1, z.2.1)) ∧
    ∀ z ∈ (univ ×ˢ Icc (-1 : ℝ) 1 : Set (UnitTwoSphere × ℝ)),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ Psi z := by
  let height : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    { toFun := fun u => t0 + rho * u
      invFun := fun t => (t - t0) / rho
      left_inv := by
        intro u
        field_simp [hrho.ne']
        ring
      right_inv := by
        intro t
        field_simp [hrho.ne']
        ring
      contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
      contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const rho).contMDiff }
  let A := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr height
  let Psi := fun z : UnitTwoSphere × ℝ =>
    threeSphereStereographic p0 (L (z.1, t0 + rho * z.2))
  obtain ⟨_, _, _, hchartloc, hchartinj⟩ :=
    projective_collar_stereographic_control p0 hp0 hD hloc hinj
  have hAmap : MapsTo A (univ ×ˢ Icc (-1 : ℝ) 1) (univ ×ˢ Ioo a b) := by
    intro z hz
    change (z.1, t0 + rho * z.2) ∈ univ ×ˢ Ioo a b
    have hlo := mul_le_mul_of_nonneg_left hz.2.1 hrho.le
    have hhi := mul_le_mul_of_nonneg_left hz.2.2 hrho.le
    exact ⟨mem_univ _, by nlinarith, by nlinarith⟩
  have hclosedloc (z : UnitTwoSphere × ℝ) (hz : z ∈ univ ×ˢ Icc (-1 : ℝ) 1) :
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ Psi z :=
    (A.isLocalDiffeomorph z).comp 𝓘(ℝ, E3) E3 (hchartloc ⟨A z, hAmap hz⟩)
  have hclosedinj : InjOn Psi (univ ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz w hw heq
    exact A.injective (hchartinj (hAmap hz) (hAmap hw) heq)
  have hsubset : (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (UnitTwoSphere × ℝ)) ⊆
      univ ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hz => ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  have hopenloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
      Psi (univ ×ˢ Ioo (-1 : ℝ) 1) :=
    fun z => hclosedloc z.1 (hsubset z.2)
  refine ⟨⟨hopenloc.contMDiffOn, hclosedinj.mono hsubset, ?_⟩, ?_, hclosedloc⟩
  · intro z hz
    exact ((hopenloc ⟨z, hz⟩).mfderivToContinuousLinearEquiv (by simp)).injective
  · have hcont : ContinuousOn Psi (univ ×ˢ Icc (-1 : ℝ) 1) :=
      fun z hz => (hclosedloc z hz).contMDiffAt.continuousAt.continuousWithinAt
    have hcontslab : Continuous
        (fun z : UnitTwoSphere × Icc (-1 : ℝ) 1 => Psi (z.1, z.2.1)) :=
      hcont.comp_continuous
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
        (fun z => ⟨mem_univ _, z.2.2⟩)
    apply hcontslab.isClosedEmbedding
    intro z w hzw
    have heq := hclosedinj ⟨mem_univ _, z.2.2⟩ ⟨mem_univ _, w.2.2⟩ hzw
    exact Prod.ext (congrArg (fun v : UnitTwoSphere × ℝ => v.1) heq)
      (Subtype.ext (congrArg (fun v : UnitTwoSphere × ℝ => v.2) heq))

end PoincareConjecture.M25.Topology3D
