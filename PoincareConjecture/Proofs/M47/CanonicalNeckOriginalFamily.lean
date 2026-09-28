import PoincareConjecture.Proofs.M47.CanonicalNeckSourceTransfer
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderOrdinary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M47

theorem strongNeck_original_ordinary_family
    {F : SurgeryFlowData.{u}} {T epsilon a b : ℝ} {J : Set ℝ}
    (N : SurgeryStrongNeck F T epsilon)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = N.neck.carrier)
    (E : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a b) U)
    (G : RicciFlow 3 U J)
    (hmetric : ∀ (s : ℝ) (hs : s ∈ Icc a b) (x : U)
      (v w : TangentSpace (𝓡 3) x),
      (F.metric (T + s / 1)).inner (E.forward s hs x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => E.forward s hs y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => E.forward s hs y.val) x w) =
          (G.metric (T + s / 1)).inner x v w)
    (htimes : ∀ s ∈ Ioc (-1 : ℝ) 0, s / (N.neck.scale⁻¹ ^ 2) ∈ Icc a b)
    (hagree : ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
      (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc a b), ∀ x ∈ U,
        HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x))
    (N0 : EpsilonNeck (G.metric T)) (hepsilon : N0.epsilon = N.neck.epsilon)
    (hscale : N0.scale = N.neck.scale)
    (hcoordinate : ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹ →
        (N0.coordinate_map z).val = N.neck.coordinate_map z) :
    RoundCylinderFamilyClose N0.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => N0.scale⁻¹ ^ 2 *
        roundCylinderPullback (G.metric (T + s / (N0.scale⁻¹ ^ 2)))
          N0.coordinate_map z v w) := by
  have hread (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
      (x : U) (v w : TangentSpace (𝓡 3) x) :
      (G.metric (T + s / (N.neck.scale⁻¹ ^ 2))).inner x v w =
        (F.metric (T + s / (N.neck.scale⁻¹ ^ 2))).inner (N.cylinder.forward s hs x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => N.cylinder.forward s hs y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => N.cylinder.forward s hs y.val) x w) := by
    have htime : T + (s / (N.neck.scale⁻¹ ^ 2)) / 1 =
        T + s / (N.neck.scale⁻¹ ^ 2) := by rw [div_one]
    have hfunctions :
        (⟨T + (s / (N.neck.scale⁻¹ ^ 2)) / 1,
          fun y : U => E.forward (s / (N.neck.scale⁻¹ ^ 2)) (htimes s hs) y.val⟩ :
            (t : ℝ) × (U → (F.slice t).carrier)) =
          ⟨T + s / (N.neck.scale⁻¹ ^ 2), fun y : U => N.cylinder.forward s hs y.val⟩ := by
      apply Sigma.ext htime
      apply Function.hfunext rfl
      intro y y' hyy
      cases hyy
      exact hagree s hs (htimes s hs) y.val y.property
    have hpull := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.metric p.1).inner (p.2 x)
        (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
    exact (congrArg (fun t => (G.metric t).inner x v w) htime).symm.trans
      ((hmetric _ (htimes s hs) x v w).symm.trans hpull)
  rw [hepsilon, hscale, N.epsilon_eq]
  apply N.metric_comparison.congr_cylinder
  intro s hs z hz v w
  have hzN : z.2 ∈ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹ := by
    simpa only [N.epsilon_eq] using hz
  have hz0 : z.2 ∈ Ioo (-N0.epsilon⁻¹) N0.epsilon⁻¹ := by
    simpa only [hepsilon] using hzN
  have hN0d := (N0.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz0⟩)).mdifferentiableAt (by simp)
  have hlocal : (fun z : RoundCylinderSpace => (N0.coordinate_map z).val) =ᶠ[𝓝 z]
      N.neck.coordinate_map := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show z ∈ univ ×ˢ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹ from ⟨mem_univ _, hzN⟩)]
      with y hy
    exact hcoordinate y hy.2
  have hsubtype : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : U → (F.slice T).carrier) (N0.coordinate_map z) :=
    (contMDiff_subtype_val (n := ∞) (N0.coordinate_map z)).mdifferentiableAt (by simp)
  have hcoordinateDeriv := mfderiv_comp z hsubtype hN0d
  have hlocalDeriv :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (fun z : RoundCylinderSpace => (N0.coordinate_map z).val) z =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.neck.coordinate_map z :=
    hlocal.mfderiv_eq
  have hsubtypeChain :
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier)
        (N0.coordinate_map z)).comp
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N0.coordinate_map z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.neck.coordinate_map z :=
    hcoordinateDeriv.symm.trans hlocalDeriv
  have hx : (N0.coordinate_map z).val ∈ N.neck.carrier := by
    rw [← hU]
    exact (N0.coordinate_map z).property
  have hfd := ((N.cylinder.forward_smooth s hs).contMDiffAt
    (N.neck.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hforwardChain := mfderiv_comp (N0.coordinate_map z) hfd hsubtype
  change mfderiv (𝓡 3) (𝓡 3)
    (fun y : U => N.cylinder.forward s hs y.val) (N0.coordinate_map z) = _ at hforwardChain
  have hread0 := hread s hs (N0.coordinate_map z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N0.coordinate_map z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N0.coordinate_map z w)
  rw [hforwardChain] at hread0
  simp only [ContinuousLinearMap.comp_apply] at hread0
  have hv := congrArg (fun A => A v) hsubtypeChain
  have hw := congrArg (fun A => A w) hsubtypeChain
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [hv, hw, hcoordinate z hzN] at hread0
  simp only [surgeryCylinderPullback, dif_pos hs, SurgeryFlowCylinder.pullbackInner,
    roundCylinderPullback]
  exact congrArg (fun r : ℝ => N.neck.scale⁻¹ ^ 2 * r) hread0.symm

end PoincareConjecture.Proofs.M47
