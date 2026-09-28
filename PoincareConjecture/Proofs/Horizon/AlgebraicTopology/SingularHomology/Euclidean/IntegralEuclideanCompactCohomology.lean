import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Euclidean.IntegralEuclideanCohomology

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Metric Set TopologicalSpace

namespace Poincare.Topology

def integralEuclideanZeroBallCompact (r : Real) :
    Compacts (EuclideanSpace Real (Fin 3)) :=
  ⟨closedBall 0 r, isCompact_closedBall 0 r⟩

set_option maxHeartbeats 1000000 in

theorem integralEuclideanZeroBallCohomologyPushforward_isIso
    (r R : Real) (hr : 0 ≤ r) (hrR : r ≤ R) (q : Nat) :
    IsIso (integralSupportCohomologyPushforward
      (closedBall_subset_closedBall hrR :
        closedBall (0 : EuclideanSpace Real (Fin 3)) r ⊆ closedBall 0 R) q) := by
  let h0r : ({0} : Set (EuclideanSpace Real (Fin 3))) ⊆ closedBall 0 r :=
    singleton_subset_iff.mpr (mem_closedBall_self hr)
  let f := integralSupportRestriction
    (closedBall_subset_closedBall hrR :
      closedBall (0 : EuclideanSpace Real (Fin 3)) r ⊆ closedBall 0 R)
  let g := integralSupportRestriction h0r
  let : QuasiIso g := integralCompactConvexSupportRestriction_quasiIso
    (closedBall 0 r) (isCompact_closedBall 0 r) (convex_closedBall 0 r) 0
      (mem_closedBall_self hr)
  have hfg : QuasiIso (f ≫ g) := by
    rw [show f ≫ g = integralSupportRestriction
      (h0r.trans (closedBall_subset_closedBall hrR)) from integralSupportRestriction_comp _ _]
    exact integralCompactConvexSupportRestriction_quasiIso
      (closedBall 0 R) (isCompact_closedBall 0 R) (convex_closedBall 0 R) 0
        (mem_closedBall_self (hr.trans hrR))
  let : QuasiIso (f ≫ g) := hfg
  have hf : QuasiIso f := quasiIso_of_comp_right f g
  let : QuasiIso (integralDualMap f) := integralRelative_dual_quasiIso _ _ f hf
  change IsIso (homologyMap (integralDualMap f) q)
  infer_instance

set_option maxHeartbeats 1000000 in

theorem integralEuclideanZeroBallCompactClass_isIso
    (r : Real) (hr : 0 ≤ r) (q : Nat) :
    IsIso (integralCompactSupportCohomologyClass (integralEuclideanZeroBallCompact r) q) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨P, hrP, hPzero⟩ := (integralCompactSupportCohomologyClass_eq_zero_iff a).mp ha
    obtain ⟨R, hrR, hPR⟩ := P.isCompact.isBounded.subset_closedBall_lt r
      (0 : EuclideanSpace Real (Fin 3))
    let Q := integralEuclideanZeroBallCompact R
    have hPQ : P ≤ Q := hPR
    have hrQ : integralEuclideanZeroBallCompact r ≤ Q := closedBall_subset_closedBall hrR.le
    let := integralEuclideanZeroBallCohomologyPushforward_isIso r R hr hrR.le q
    have hinj : Function.Injective (integralSupportCohomologyPushforward hrQ q) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply (injective_iff_map_eq_zero _).mp hinj a
    have he := congrArg (fun f => f a)
      (integralSupportCohomologyPushforward_comp hrP hPQ q)
    change integralSupportCohomologyPushforward hPQ q
      (integralSupportCohomologyPushforward hrP q a) =
        integralSupportCohomologyPushforward hrQ q a at he
    rw [hPzero, map_zero] at he
    exact he.symm
  · intro a
    obtain ⟨K, b, hb⟩ := exists_integralCompactSupportCohomology_representative q a
    obtain ⟨R, hrR, hKR⟩ := K.isCompact.isBounded.subset_closedBall_lt r
      (0 : EuclideanSpace Real (Fin 3))
    let Q := integralEuclideanZeroBallCompact R
    have hKQ : K ≤ Q := hKR
    have hrQ : integralEuclideanZeroBallCompact r ≤ Q := closedBall_subset_closedBall hrR.le
    let := integralEuclideanZeroBallCohomologyPushforward_isIso r R hr hrR.le q
    obtain ⟨b', hb'⟩ := (ModuleCat.epi_iff_surjective
      (integralSupportCohomologyPushforward hrQ q)).mp inferInstance
        (integralSupportCohomologyPushforward hKQ q b)
    refine ⟨b', ?_⟩
    calc
      integralCompactSupportCohomologyClass (integralEuclideanZeroBallCompact r) q b' =
          integralCompactSupportCohomologyClass Q q
            (integralSupportCohomologyPushforward hrQ q b') :=
        (congrArg (fun f => f b')
          (integralCompactSupportCohomologyClass_pushforward hrQ q)).symm
      _ = integralCompactSupportCohomologyClass Q q
            (integralSupportCohomologyPushforward hKQ q b) := congrArg _ hb'
      _ = integralCompactSupportCohomologyClass K q b :=
        congrArg (fun f => f b) (integralCompactSupportCohomologyClass_pushforward hKQ q)
      _ = a := hb

set_option maxHeartbeats 1000000 in

theorem integralEuclideanCompactSupportCohomology_ne_three_isZero
    (q : Nat) (hq : q ≠ 3) :
    IsZero (integralCompactSupportCohomology (EuclideanSpace Real (Fin 3)) q) := by
  let := integralEuclideanZeroBallCompactClass_isIso 1 (by norm_num) q
  exact (integralEuclideanZeroBallCohomology_ne_three_isZero 1 (by norm_num) q hq).of_iso
    (asIso (integralCompactSupportCohomologyClass (integralEuclideanZeroBallCompact 1) q)).symm

def integralEuclideanCompactSupportCohomologyThreeEquiv :
    integralCompactSupportCohomology (EuclideanSpace Real (Fin 3)) 3 ≃ₗ[Int] ULift Int := by
  let := integralEuclideanZeroBallCompactClass_isIso 1 (by norm_num) 3
  exact (asIso (integralCompactSupportCohomologyClass
    (integralEuclideanZeroBallCompact 1) 3)).symm.toLinearEquiv.trans
      (integralEuclideanZeroBallCohomologyThreeEquiv 1 (by norm_num))

end Poincare.Topology
