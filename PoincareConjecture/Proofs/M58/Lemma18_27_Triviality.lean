import PoincareConjecture.Proofs.M58.Lemma18_27_FamilyContraction
import PoincareConjecture.Proofs.M58.Lemma18_27_ShortFamilies
import PoincareConjecture.Proofs.M58.BasedCone










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem short_loop_family_trivial (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) (basepoint : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M basepoint)) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ source : FreeTwoSphereFamily (M := M),
      source.basepoint = basepoint →
      (∀ c, freeLoopLength g (source.family c) < ζ) → source.homotopy_class = 1 := by
  obtain ⟨ζ, hζ, hcontract⟩ := exists_short_family_contraction g hcompact
  refine ⟨ζ, hζ, ?_⟩
  intro source hbase hlength
  obtain ⟨H, h0, h1, hfixed⟩ :=
    hcontract ⟨source.family, source.continuous⟩ hlength
  exact family_class_eq_one_of_contraction source (by simpa only [hbase] using hpi)
    loopCircleBasepoint H h0 h1 (fun t c hc => hfixed t c source.basepoint hc)




theorem raw_short_loop_family_trivial (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) (hconnected : IsConnected (univ : Set M))
    (basepoint : M) (hpi : Subsingleton (HomotopyGroup.Pi 2 M basepoint)) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ source : C(LoopTwoSphere, C1FreeLoopSpace (M := M)),
      (∀ c, freeLoopLength g (source c) < ζ) →
        source.Homotopic (constantLoopFamily basepoint) := by
  obtain ⟨ζ, hζ, hcontract⟩ := exists_short_family_contraction g hcompact
  refine ⟨ζ, hζ, ?_⟩
  intro source hlength
  obtain ⟨H, h0, h1, -⟩ := hcontract source hlength
  apply raw_family_homotopic_const_of_contraction hconnected basepoint hpi
    loopCircleBasepoint source
  exact ⟨{ toFun := H
           continuous_toFun := H.continuous
           map_zero_left := h0
           map_one_left := h1 }⟩

end PoincareConjecture.Proofs.M58
