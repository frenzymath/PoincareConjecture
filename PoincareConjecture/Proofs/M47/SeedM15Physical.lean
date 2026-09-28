import PoincareConjecture.Proofs.M47.SeedM15Radius
import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M47.SeedM15Subtype










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47




theorem seedM15_physical_volume
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    {taubar l0 V epsilon age : ℝ} (Q : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (hepsilon : 0 < epsilon) (hage : 0 < age)
    {F : SurgeryFlowData.{u}} {origin a tau r : ℝ} (ha : a < 0)
    (U : TopologicalSpace.Opens (F.slice origin).carrier)
    [CompactSpace U] [ConnectedSpace U]
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc a 0) U)
    (he : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (G : RicciFlow 3 U (Icc (origin + a) origin))
    (hmetric : ∀ s (hs : s ∈ Icc a 0) (y : U) (v w : TangentSpace (𝓡 3) y),
      (F.metric (origin + s / 1)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
          (G.metric (origin + s / 1)).inner y v w)
    (hnorm : ∀ s (hs : s ∈ Icc a 0) (y : U),
      (G.connection (origin + s / 1)).curvatureTensorNorm y =
        (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs y.val))
    (x : U) (htauAge : tau < -a) (htauTop : tau ≤ taubar) (hageTau : age ≤ tau)
    (A : Set U) (hA : IsOpen A)
    (haccess : ∀ y ∈ A, reducedLength G origin x y tau ≤ l0)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume (G.metric (origin - tau)) A)
    (hr : 0 < r) (hrepsilon : r ≤ epsilon)
    (test : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc (-r ^ 2) 0)
      ((F.metric origin).ball x.val r))
    (hbased : ∀ hs y, y ∈ (F.metric origin).ball x.val r →
      HEq (test.forward 0 hs y) y)
    (hcurv : ∀ s (hs : s ∈ Icc (-r ^ 2) 0),
      ∀ y ∈ (F.metric origin).ball x.val r,
        (F.connection (origin + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal ((Q.kappa * Proofs.M47.seedRadiusFactor epsilon age ^ 3) * r ^ 3) ≤
      calibratedMetricVolume (F.metric origin) ((F.metric origin).ball x.val r) := by
  have hterminal (y : U) (v w : TangentSpace (𝓡 3) y) :
      (G.metric origin).inner y v w = (F.metric origin).inner y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) y w) := by
    have hfunctions :
        (⟨origin + 0 / 1, fun z : U => e.forward 0 ⟨ha.le, le_rfl⟩ z.val⟩ :
          (t : ℝ) × (U → (F.slice t).carrier)) =
            ⟨origin, (Subtype.val : U → (F.slice origin).carrier)⟩ := by
      apply Sigma.ext (by simp)
      apply Function.hfunext rfl
      intro z z' hzz
      cases hzz
      exact he _ z.val z.property
    have hpull := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.metric p.1).inner (p.2 y)
        (mfderiv (𝓡 3) (𝓡 3) p.2 y v) (mfderiv (𝓡 3) (𝓡 3) p.2 y w)) hfunctions
    exact (congrArg (fun t => (G.metric t).inner y v w)
      (show origin + 0 / 1 = origin by simp)).symm.trans
        ((hmetric 0 ⟨ha.le, le_rfl⟩ y v w).symm.trans hpull)
  have hball := seedM15_subtype_ball_image U (G.metric origin) (F.metric origin) hterminal x r
  have hcurvG : ∀ t ∈ Icc (origin + a) origin, origin - r ^ 2 ≤ t →
      ∀ y ∈ (G.metric origin).ball x r, (G.connection t).curvatureTensorNorm y ≤ r⁻¹ ^ 2 := by
    intro t ht htr y hy
    have hs : t - origin ∈ Icc a 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsTest : t - origin ∈ Icc (-r ^ 2) 0 := ⟨by linarith, hs.2⟩
    have hI : Icc (t - origin) 0 ⊆ Icc a 0 := Icc_subset_Icc hs.1 le_rfl
    have hJ : Icc (t - origin) 0 ⊆ Icc (-r ^ 2) 0 := Icc_subset_Icc hsTest.1 le_rfl
    have hyPhysical : y.val ∈ (F.metric origin).ball x.val r := hball ⟨y, hy, rfl⟩
    have hagree : e.forward (t - origin) hs y.val =
        test.forward (t - origin) hsTest y.val :=
      seedM15_cylinder_eq_of_terminal e test hs.2 hI hJ y.val y.property y.val hyPhysical
        (eq_of_heq ((he _ y.val y.property).trans (hbased _ y.val hyPhysical).symm))
    have hc : origin + (t - origin) / 1 = t := by simp only [div_one, add_sub_cancel]
    have hn : (G.connection t).curvatureTensorNorm y =
        (F.connection (origin + (t - origin) / 1)).curvatureTensorNorm
          (e.forward (t - origin) hs y.val) :=
      (congrArg (fun s => (G.connection s).curvatureTensorNorm y) hc).symm.trans
        (hnorm (t - origin) hs y)
    rw [hn, hagree]
    exact hcurv (t - origin) hsTest y.val hyPhysical
  have hvol := seedM15_ordinary_radius_volume hM12 hM13 hM14 hOrdinary Q hepsilon hage
    (by linarith : origin + a < origin) G x (by linarith) htauTop hageTau
    A hA haccess hvolume hr hrepsilon hcurvG
  exact hvol.trans
    (seedM15_subtype_ball_volume U (G.metric origin) (F.metric origin) hterminal x r)

end PoincareConjecture.M47
