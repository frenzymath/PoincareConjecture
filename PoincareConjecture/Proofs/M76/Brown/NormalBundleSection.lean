import PoincareConjecture.Proofs.M76.Brown.NormalBundleCore
import Mathlib.Topology.Homotopy.Lifting








set_option autoImplicit false

open Set Bundle

namespace BrownCollar.FlatteningAtlas

variable {X P ι : Type*} [TopologicalSpace X] [NormedAddCommGroup P]
  [NormedSpace ℝ P] {S : Set X} (A : FlatteningAtlas P S ι)
  [SimplyConnectedSpace S] [LocallyPathConnectedSpace S] [Nonempty S]




theorem exists_normalBundle_section :
    ∃ sigma : C(S, A.normalBundleCore.TotalSpace),
      ∀ x, A.normalBundleCore.proj (sigma x) = x := by
  let x0 : S := Classical.choice inferInstance
  let e0 : A.normalBundleCore.TotalSpace := ⟨x0, (1 : SignTypeˣ)⟩
  obtain ⟨sigma, ⟨_, hsigma⟩, _⟩ :=
    A.normalBundle_isCoveringMap.existsUnique_continuousMap_lifts
      (ContinuousMap.id S) x0 e0 rfl
  exact ⟨sigma, fun x => congrFun hsigma x⟩




theorem exists_coherent_normal_units :
    ∃ a : ι → S → SignTypeˣ,
      (∀ i, ContinuousOn (a i) (A.baseSet i)) ∧
      ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
        a j x = A.transitionUnit i j x * a i x := by
  obtain ⟨sigma, hsigma⟩ := A.exists_normalBundle_section
  let a : ι → S → SignTypeˣ := fun i x => (A.normalBundleCore.localTriv i (sigma x)).2
  refine ⟨a, ?_, ?_⟩
  · intro i
    have hsource : ∀ x ∈ A.baseSet i,
        sigma x ∈ (A.normalBundleCore.localTriv i).source := by
      intro x hx
      change (sigma x).proj ∈ A.baseSet i
      have hp : (sigma x).proj = x := hsigma x
      rwa [hp]
    exact ((A.normalBundleCore.localTriv i).continuousOn.comp
      sigma.continuous.continuousOn hsource).snd
  · intro i j x hx
    have hp : (sigma x).proj = x := hsigma x
    change A.normalBundleCore.coordChange
        (A.normalBundleCore.indexAt (sigma x).proj) j (sigma x).proj (sigma x).snd =
      A.transitionUnit i j x * A.normalBundleCore.coordChange
        (A.normalBundleCore.indexAt (sigma x).proj) i (sigma x).proj (sigma x).snd
    rw [hp]
    exact (A.normalBundleCore.coordChange_comp (A.normalBundleCore.indexAt x) i j x
      ⟨⟨A.normalBundleCore.mem_baseSet_at x, hx.1⟩, hx.2⟩ (sigma x).snd).symm

end BrownCollar.FlatteningAtlas
