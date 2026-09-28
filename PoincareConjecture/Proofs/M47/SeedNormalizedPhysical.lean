import PoincareConjecture.Proofs.M47.SeedNormalizedRadius
import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M47.SeedM15Subtype
import PoincareConjecture.Proofs.M47.CanonicalNeckTerminalMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47



theorem seedM15_normalized_physical_volume
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    {l0 V : ℝ} (Q : M15GeneralizedUniformData.{u} 3 1 l0 V)
    {F : SurgeryFlowData.{u}} {T a tau r : ℝ} (ha : a < 0)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    [CompactSpace U] [ConnectedSpace U]
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U)
    (he : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (G : RicciFlow 3 U (Icc (T + a) T))
    (hmetric : ∀ s (hs : s ∈ Icc a 0) (y : U) (v w : TangentSpace (𝓡 3) y),
      (F.metric (T + s / 1)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
          (G.metric (T + s / 1)).inner y v w)
    (hnorm : ∀ s (hs : s ∈ Icc a 0) (y : U),
      (G.connection (T + s / 1)).curvatureTensorNorm y =
        (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y.val))
    (x : U) (htauAge : tau < -a) (hlo : 3 * (-a) / 4 ≤ tau)
    (E : Set U) (hE : IsOpen E)
    (haccess : ∀ y ∈ E, reducedLength G T x y tau ≤ l0)
    (hvolume : ENNReal.ofReal (V * Real.sqrt (-a) ^ 3) ≤
      calibratedMetricVolume (G.metric (T - tau)) E)
    (hr : 0 < r) (hsize : r ^ 2 ≤ 8 * (-a))
    (test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
      ((F.metric T).ball x.val r))
    (hbased : ∀ hs y, y ∈ (F.metric T).ball x.val r → HEq (test.forward 0 hs y) y)
    (hcurv : ∀ s (hs : s ∈ Icc (-r ^ 2) 0), ∀ y ∈ (F.metric T).ball x.val r,
      (F.connection (T + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal ((Q.kappa / 64) * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x.val r) := by
  have hterminal := neck_ordinary_terminal_metric U e ⟨ha.le, le_rfl⟩ he G
    (hmetric 0 ⟨ha.le, le_rfl⟩)
  have hball := seedM15_subtype_ball_image U (G.metric T) (F.metric T) hterminal x r
  have hcurvG : ∀ t ∈ Icc (T + a) T, T - r ^ 2 ≤ t →
      ∀ y ∈ (G.metric T).ball x r, (G.connection t).curvatureTensorNorm y ≤ r⁻¹ ^ 2 := by
    intro t ht htr y hy
    have hs : t - T ∈ Icc a 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsTest : t - T ∈ Icc (-r ^ 2) 0 := ⟨by linarith, hs.2⟩
    have hI : Icc (t - T) 0 ⊆ Icc a 0 := Icc_subset_Icc hs.1 le_rfl
    have hJ : Icc (t - T) 0 ⊆ Icc (-r ^ 2) 0 := Icc_subset_Icc hsTest.1 le_rfl
    have hyPhysical : y.val ∈ (F.metric T).ball x.val r := hball ⟨y, hy, rfl⟩
    have hagree : e.forward (t - T) hs y.val = test.forward (t - T) hsTest y.val :=
      seedM15_cylinder_eq_of_terminal e test hs.2 hI hJ y.val y.property y.val hyPhysical
        (eq_of_heq ((he _ y.val y.property).trans (hbased _ y.val hyPhysical).symm))
    have hc : T + (t - T) / 1 = t := by simp
    have hn : (G.connection t).curvatureTensorNorm y =
        (F.connection (T + (t - T) / 1)).curvatureTensorNorm (e.forward (t - T) hs y.val) :=
      (congrArg (fun s => (G.connection s).curvatureTensorNorm y) hc).symm.trans
        (hnorm (t - T) hs y)
    rw [hn, hagree]
    exact hcurv (t - T) hsTest y.val hyPhysical
  have hage : T - (T + a) = -a := by ring
  have hv := seedM15_normalized_radius_volume hM12 hM13 hM14 hOrdinary Q
    (by linarith : T + a < T) G x (by rwa [hage]) (by rwa [hage])
    E hE haccess (by rwa [hage]) hr (by rwa [hage]) hcurvG
  exact hv.trans (seedM15_subtype_ball_volume U (G.metric T) (F.metric T) hterminal x r)

end PoincareConjecture.Proofs.M47
