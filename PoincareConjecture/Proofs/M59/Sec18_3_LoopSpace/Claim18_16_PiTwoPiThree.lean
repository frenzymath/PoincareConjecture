import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.C1ValueComparison
import PoincareConjecture.Proofs.M59.Mathlib.ContinuousLoopComparison
import PoincareConjecture.Proofs.M59.Mathlib.CubicalMapNaturality
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.SystemAssembly










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u v

namespace PoincareConjecture

open Proofs.M02 Proofs.M59

section ValueMap

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] [T2Space M]



def m59C1ValueEquivTop (hcompact : IsCompact (univ : Set M))
    (n : Nat) [Nonempty (Fin n)] (x : M) :
    HomotopyGroup.Pi n (C1FreeLoopSpace (M := M)) (constantC1Loop x) ≃*
      HomotopyGroup.Pi n C(LoopCircle, M) (ContinuousMap.const LoopCircle x) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  exact m59C1ValueEquiv hcompact n x



theorem m59C1ValueEquivTop_apply (hcompact : IsCompact (univ : Set M))
    (n : Nat) [Nonempty (Fin n)] (x : M)
    (a : HomotopyGroup.Pi n (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    m59C1ValueEquivTop hcompact n x a = homotopyGroupMap (Fin n) Proofs.M58.loopValues rfl a := rfl

end ValueMap



def m59BasedLoopAdjunction {X : Type u} [TopologicalSpace X] (x : X) :
    HomotopyGroup.Pi 2 (GenLoop (Fin 1) X x) GenLoop.const ≃* HomotopyGroup.Pi 3 X x :=
  (HomotopyGroup.cubicalAdjunction x).trans
    (HomotopyGroup.reindex x (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3))



theorem m59BasedLoopAdjunction_naturality
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup.Pi 2 (GenLoop (Fin 1) X x) GenLoop.const) :
    m59BasedLoopAdjunction y
      (homotopyGroupMap (Fin 2) (mapGenLoopMap (Fin 1) f h)
        (mapGenLoopMap_const (Fin 1) f h) a) =
      homotopyGroupMap (Fin 3) f h (m59BasedLoopAdjunction x a) := by
  refine Quotient.inductionOn a fun a => ?_
  change (⟦GenLoop.congr y finSumFinEquiv (GenLoop.genLoopGenLoopEquiv y
    (mapGenLoop (mapGenLoopMap (Fin 1) f h) (mapGenLoopMap_const (Fin 1) f h) a))⟧ :
    HomotopyGroup.Pi 3 Y y) =
      ⟦mapGenLoop f h (GenLoop.congr x finSumFinEquiv (GenLoop.genLoopGenLoopEquiv x a))⟧
  rw [genLoopGenLoopEquiv_map, genLoop_congr_map]

section Comparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] [T2Space M]



def m59PiTwoPiThree (hcompact : IsCompact (univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) :
    HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x) ≃*
      HomotopyGroup.Pi 3 M x :=
  (m59C1ValueEquivTop hcompact 2 x).trans
    ((m59CircleQuotient.continuousLoopEquiv x hpi).symm.trans (m59BasedLoopAdjunction x))

variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N] [T2Space N]



theorem m59C1ValueEquivTop_naturality
    (hcompactM : IsCompact (univ : Set M)) (hcompactN : IsCompact (univ : Set N))
    (n : Nat) [Nonempty (Fin n)] {x : M} {y : N}
    (f : C(M, N)) (h : f x = y) (L : M59LoopPostcomposition f)
    (a : HomotopyGroup.Pi n (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    m59C1ValueEquivTop hcompactN n y
      (surgeryHomotopyMap L.map (L.map_based h) a) =
    homotopyGroupMap (Fin n) (postcomposeMap LoopCircle f) (postcomposeMap_const LoopCircle f h)
      (m59C1ValueEquivTop hcompactM n x a) := by
  refine Quotient.inductionOn a fun a => ?_
  change (⟦mapGenLoop Proofs.M58.loopValues rfl (surgeryMappedGenLoop L.map (L.map_based h) a)⟧ :
    HomotopyGroup.Pi n C(LoopCircle, N) (ContinuousMap.const LoopCircle y)) =
    ⟦mapGenLoop (postcomposeMap LoopCircle f) (postcomposeMap_const LoopCircle f h)
      (mapGenLoop Proofs.M58.loopValues rfl a)⟧
  apply congrArg
    (fun b => (⟦b⟧ : HomotopyGroup.Pi n C(LoopCircle, N) (ContinuousMap.const LoopCircle y)))
  ext w z
  exact m59LoopPostcomposition_apply L (a w) z



theorem m59PiTwoPiThree_naturality
    (hcompactM : IsCompact (univ : Set M)) (hcompactN : IsCompact (univ : Set N))
    (x : M) (y : N)
    (hpiM : Subsingleton (HomotopyGroup.Pi 2 M x))
    (hpiN : Subsingleton (HomotopyGroup.Pi 2 N y))
    (f : C(M, N)) (h : f x = y) (L : M59LoopPostcomposition f)
    (a : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    m59PiTwoPiThree hcompactN y hpiN
      (surgeryHomotopyMap (n := 2) L.map (L.map_based h) a) =
      surgeryHomotopyMap (n := 3) f h (m59PiTwoPiThree hcompactM x hpiM a) := by
  let VM := m59C1ValueEquivTop hcompactM 2 x
  let VN := m59C1ValueEquivTop hcompactN 2 y
  let DM := m59CircleQuotient.continuousLoopEquiv x hpiM
  let DN := m59CircleQuotient.continuousLoopEquiv y hpiN
  let B := homotopyGroupMap (Fin 2) (mapGenLoopMap (Fin 1) f h) (mapGenLoopMap_const (Fin 1) f h)
  let F := homotopyGroupMap (Fin 2) (postcomposeMap LoopCircle f)
    (postcomposeMap_const LoopCircle f h)
  let b := DM.symm (VM a)
  have hb : DM b = VM a := DM.apply_symm_apply (VM a)
  have hD (c) : DN (B c) = F (DM c) :=
    homotopyGroupMap_descend_naturality m59CircleQuotient f h c
  have hV : VN (surgeryHomotopyMap L.map (L.map_based h) a) = F (VM a) :=
    m59C1ValueEquivTop_naturality hcompactM hcompactN 2 f h L a
  have hn : DN.symm (VN (surgeryHomotopyMap L.map (L.map_based h) a)) = B b := by
    apply DN.injective
    rw [DN.apply_symm_apply, hD, hb]
    exact hV
  change m59BasedLoopAdjunction y (DN.symm (VN (surgeryHomotopyMap L.map (L.map_based h) a))) =
    surgeryHomotopyMap (n := 3) f h (m59BasedLoopAdjunction x b)
  rw [hn]
  exact m59BasedLoopAdjunction_naturality f h b

end Comparison



def m59ComparisonService : M59ComparisonService.{u} where
  comparison compact _connected x piTwo := m59PiTwoPiThree compact x piTwo
  naturality compactM _connectedM compactN _connectedN x y piTwoM piTwoN f _smooth based L a :=
    m59PiTwoPiThree_naturality compactM compactN x y piTwoM piTwoN f based L a



def m59IdentificationSystem_of_free_class
    (hfree : M59FreeClassFaithfulness.{u} m59SphereQuotient) : M59IdentificationSystem.{u} :=
  m59IdentificationSystem_of_comparison_and_free_class m59ComparisonService hfree

end PoincareConjecture
