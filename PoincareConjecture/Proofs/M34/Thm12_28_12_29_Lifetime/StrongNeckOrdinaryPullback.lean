import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckOrdinaryCylinder
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

variable {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {K : Set ℝ} {U : Set C.carrier}

theorem ordinaryChapter11PushedCylinder_pullbackInner_eq
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K)
    (base : C.carrier) (hzero : 0 ∈ K) {V : Set C.carrier}
    (hV : IsOpen V) (hVU : V ⊆ U)
    (K' : Set ℝ) (hK' : K' ⊆ K) (hK'conn : IsPreconnected K') (hzero' : 0 ∈ K')
    {s : ℝ} (hs : s ∈ K') {x : C.carrier} (hx : x ∈ V)
    (v w : TangentSpace (𝓡 3) x) :
    (ordinaryChapter11PushedCylinder R e base hzero V K' hK').pullbackInner s hs
      (e.forward 0 hzero x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x w) =
      e.pullbackInner s (hK' hs) x v w := by
  let e' := ordinaryChapter11PushedCylinder R e base hzero V K' hK'
  let f := ordinaryChapter11CylinderSpatialMap R e 0 hzero
  let f' := ordinaryChapter11CylinderSpatialMap R e' 0 hzero'
  have hV' : IsOpen (e.forward 0 hzero '' V) := e.isOpen_forward_image hU hV hVU hzero
  have hx' : e.forward 0 hzero x ∈ e.forward 0 hzero '' V := mem_image_of_mem _ hx
  have he := ((e.forward_smooth 0 hzero).contMDiffAt
    (hU.mem_nhds (hVU hx))).mdifferentiableAt (by simp)
  have hf' := ((ordinaryChapter11CylinderSpatialMap_contMDiffOn R e' hzero').contMDiffAt
    (hV'.mem_nhds hx')).mdifferentiableAt (by simp)
  have hcomp : f' ∘ e.forward 0 hzero = f :=
    ordinaryChapter11PushedCylinder_spatialMap_comp R e base hzero V K' hK' hzero'
  have hlocal : f' ∘ e.forward 0 hzero =ᶠ[𝓝 x] f :=
    Filter.Eventually.of_forall (congrFun hcomp)
  have hd : (mfderiv (𝓡 3) (𝓡 3) f' (e.forward 0 hzero x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x) = mfderiv (𝓡 3) (𝓡 3) f x :=
    (mfderiv_comp x hf' he).symm.trans hlocal.mfderiv_eq
  have hnew := ordinaryChapter11Cylinder_pullbackInner_eq R e' hV' hK'conn
    hzero' hs hx'
    (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x w)
  have hold := ordinaryChapter11Cylinder_pullbackInner_eq R e hU hK
    hzero (hK' hs) (hVU hx) v w
  refine hnew.trans (?_ : _ = e.pullbackInner s (hK' hs) x v w)
  rw [hold]
  change scale * (F.metric ((origin + 0 / scale) + s / scale)).inner
      (f' (e.forward 0 hzero x))
      ((mfderiv (𝓡 3) (𝓡 3) f' (e.forward 0 hzero x))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x v))
      ((mfderiv (𝓡 3) (𝓡 3) f' (e.forward 0 hzero x))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x w)) =
    scale * (F.metric (origin + s / scale)).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
  rw [show (origin + 0 / scale) + s / scale = origin + s / scale by simp]
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  apply congrArg (fun a : ℝ => scale * a)
  exact (congrArg₂ (fun V W : E₃ => (F.metric (origin + s / scale)).inner
    (f' (e.forward 0 hzero x)) V W) hv hw).trans
      (congrArg (fun y : M => (F.metric (origin + s / scale)).inner y
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
        (congrFun hcomp x))

theorem ordinaryChapter11PushedCylinder_cylinderPullback_eq
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K)
    (base : C.carrier) (hzero : 0 ∈ K) {V : Set C.carrier}
    (hV : IsOpen V) (hVU : V ⊆ U)
    (K' : Set ℝ) (hK' : K' ⊆ K) (hK'conn : IsPreconnected K') (hzero' : 0 ∈ K')
    {s : ℝ} (hs : s ∈ K') {coordinate : RoundCylinderSpace → C.carrier}
    {z : RoundCylinderSpace}
    (hcoordinate : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z)
    (hz : coordinate z ∈ V) (v w : RoundCylinderTangent z) :
    generalizedCylinderPullback
      (ordinaryChapter11PushedCylinder R e base hzero V K' hK')
      (e.forward 0 hzero ∘ coordinate) s z v w =
      generalizedCylinderPullback e coordinate s z v w := by
  have he := ((e.forward_smooth 0 hzero).contMDiffAt
    (hU.mem_nhds (hVU hz))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z he hcoordinate
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  simp only [generalizedCylinderPullback, dif_pos hs, dif_pos (hK' hs), Function.comp_apply]
  exact (congrArg₂ (fun v' w' : E₃ =>
    (ordinaryChapter11PushedCylinder R e base hzero V K' hK').pullbackInner s hs
      (e.forward 0 hzero (coordinate z)) v' w') hv hw).trans
      (ordinaryChapter11PushedCylinder_pullbackInner_eq R e hU hK base hzero hV hVU
        K' hK' hK'conn hzero' hs hz
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w))

end PoincareConjecture.M34
