import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralHomologyUniverse
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralCompactGluing
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactSupport
import Mathlib.Geometry.Manifold.ChartedSpace









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open Set

universe u

namespace Poincare.Topology

theorem integralThreeManifoldCompactSupport
    {M : Type u} [TopologicalSpace M] [T2Space M] [RegularSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    (K : Set M) (hK : IsCompact K) :
    (∀ n : Nat, IsZero (integralSupportHomology K (n + 4))) ∧
      IntegralSupportDetected K 3 := by
  apply integralCompactSupport_local_to_global K hK 3
  intro x hx
  let e := chartAt (EuclideanSpace Real (Fin 3)) x
  refine ⟨e.source, e.open_source, mem_chart_source _ x, ?_⟩
  intro L hL hLs
  have himage : IsCompact (e '' L) :=
    hL.image_of_continuousOn (e.continuousOn.mono hLs)
  constructor
  · intro n
    let E := integralChartSupportHomologyEquiv e L hL hLs (n + 4)
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (integralEuclideanCompactSupportAbove_isZero (e '' L) himage n)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun a b => E.injective (hz.elim (E a) (E b))⟩
  · intro a ha
    let E := integralChartSupportHomologyEquiv e L hL hLs 3
    apply E.injective
    rw [map_zero]
    apply integralEuclideanCompactSupportThree_detected (e '' L) himage (E a)
    rintro y ⟨z, hz, rfl⟩
    have he := integralChartSupportHomologyEquiv_naturality e hL isCompact_singleton hLs
      (singleton_subset_iff.mpr (hLs hz)) (singleton_subset_iff.mpr hz) 3 a
    rw [ha z hz, map_zero] at he
    have himg : e '' ({z} : Set M) = ({e z} : Set (EuclideanSpace Real (Fin 3))) :=
      Set.image_singleton
    have hs : ({e z} : Set (EuclideanSpace Real (Fin 3))) ⊆ e '' ({z} : Set M) := by
      rw [himg]
    have hm := congrArg (fun f => f (E a))
      (integralSupportHomologyRestriction_comp hs
        (Set.image_mono (f := e) (singleton_subset_iff.mpr hz)) 3)
    change integralSupportHomologyRestriction hs 3
        (integralSupportHomologyRestriction
          (Set.image_mono (f := e) (singleton_subset_iff.mpr hz)) 3 (E a)) =
      integralSupportHomologyRestriction
        (hs.trans (Set.image_mono (f := e) (singleton_subset_iff.mpr hz))) 3 (E a) at hm
    rw [← he, map_zero] at hm
    exact hm.symm

end Poincare.Topology
