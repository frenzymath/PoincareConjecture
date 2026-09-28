import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Sign









set_option autoImplicit false

open Set Bundle

namespace BrownCollar

theorem signUnit_mul_self (s : SignTypeˣ) : s * s = 1 := by
  apply Units.ext
  exact mul_inv_cancel₀ s.ne_zero

variable {X : Type*} [TopologicalSpace X]




noncomputable def twoOpenSignCore (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) (c : X → SignTypeˣ) (hc : ContinuousOn c (A ∩ B)) :
    FiberBundleCore Bool X SignTypeˣ := by
  classical
  exact
    { baseSet := fun i => cond i B A
      isOpen_baseSet := by
        intro i
        cases i
        · exact hA
        · exact hB
      indexAt := fun x => if x ∈ A then false else true
      mem_baseSet_at := by
        intro x
        split_ifs with hx
        · exact hx
        · have hxAB : x ∈ A ∪ B := by rw [hcover]; exact mem_univ x
          exact hxAB.resolve_left hx
      coordChange := fun i j x v => if i = j then v else c x * v
      coordChange_self := fun i _ _ _ => if_pos rfl
      continuousOn_coordChange := by
        intro i j
        cases i <;> cases j
        · exact continuous_snd.continuousOn
        · exact (hc.comp continuous_fst.continuousOn (fun _ h => h.1)).mul
            continuous_snd.continuousOn
        · exact ((hc.mono (by intro x hx; exact ⟨hx.2, hx.1⟩)).comp
            continuous_fst.continuousOn (fun _ h => h.1)).mul continuous_snd.continuousOn
        · exact continuous_snd.continuousOn
      coordChange_comp := by
        intro i j k x _ v
        cases i <;> cases j <;> cases k <;> dsimp <;>
          first | rfl | rw [← mul_assoc, signUnit_mul_self, one_mul] }



theorem twoOpenSignCore_isCoveringMap (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) (c : X → SignTypeˣ) (hc : ContinuousOn c (A ∩ B)) :
    IsCoveringMap (twoOpenSignCore A B hA hB hcover c hc).proj :=
  FiberBundle.isCoveringMap




theorem exists_two_open_sign_section [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [Nonempty X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) (c : X → SignTypeˣ) (hc : ContinuousOn c (A ∩ B)) :
    ∃ a0 a1 : X → SignTypeˣ, ContinuousOn a0 A ∧ ContinuousOn a1 B ∧
      ∀ x ∈ A ∩ B, a1 x = c x * a0 x := by
  let Z := twoOpenSignCore A B hA hB hcover c hc
  let x0 : X := Classical.choice inferInstance
  let e0 : Z.TotalSpace := ⟨x0, (1 : SignTypeˣ)⟩
  obtain ⟨sigma, ⟨_, hsigma⟩, _⟩ :=
    (twoOpenSignCore_isCoveringMap A B hA hB hcover c hc).existsUnique_continuousMap_lifts
      (ContinuousMap.id X) x0 e0 rfl
  have hs (x : X) : (sigma x).proj = x := congrFun hsigma x
  let a0 : X → SignTypeˣ := fun x => (Z.localTriv false (sigma x)).2
  let a1 : X → SignTypeˣ := fun x => (Z.localTriv true (sigma x)).2
  refine ⟨a0, a1, ?_, ?_, ?_⟩
  · have hsource : ∀ x ∈ A, sigma x ∈ (Z.localTriv false).source := by
      intro x hx
      change (sigma x).proj ∈ A
      rwa [hs]
    exact ((Z.localTriv false).continuousOn.comp sigma.continuous.continuousOn hsource).snd
  · have hsource : ∀ x ∈ B, sigma x ∈ (Z.localTriv true).source := by
      intro x hx
      change (sigma x).proj ∈ B
      rwa [hs]
    exact ((Z.localTriv true).continuousOn.comp sigma.continuous.continuousOn hsource).snd
  · intro x hx
    change Z.coordChange (Z.indexAt (sigma x).proj) true (sigma x).proj (sigma x).snd =
      c x * Z.coordChange (Z.indexAt (sigma x).proj) false (sigma x).proj (sigma x).snd
    rw [hs]
    exact (Z.coordChange_comp (Z.indexAt x) false true x
      ⟨⟨Z.mem_baseSet_at x, hx.1⟩, hx.2⟩ (sigma x).snd).symm

end BrownCollar
