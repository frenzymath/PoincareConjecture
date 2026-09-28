import PoincareConjecture.Proofs.M38.SphereBundleCylinder
import PoincareConjecture.Proofs.M38.CylinderSeparator
import PoincareConjecture.Proofs.M38.CirclePullbackComponent
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

theorem sphereBundle_cut_component_precompact
    (Q : GeneralizedSliceCarrier) [CompactSpace Q.carrier] (B : SurgerySphereBundle Q)
    (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (circlePullbackCarrier Q B.projection B.projection_smooth).carrier ∞)
    (a : (circlePullbackCarrier Q B.projection B.projection_smooth).carrier) :
    let q := circlePullbackProjection Q B.projection B.projection_smooth
    IsCompact (closure (connectedComponentIn
      (q ⁻¹' (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ) a)) := by
  let A := circlePullbackCarrier Q B.projection B.projection_smooth
  let q := circlePullbackProjection Q B.projection B.projection_smooth
  let h := circlePullbackHeight Q B.projection B.projection_smooth
  let : AddAction ℤ A.carrier := inferInstanceAs (AddAction ℤ (CirclePullback B.projection))
  let : ContinuousConstVAdd ℤ A.carrier :=
    inferInstanceAs (ContinuousConstVAdd ℤ (CirclePullback B.projection))
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := StandardCapSpace)
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  obtain ⟨T, hT⟩ := exists_sphereBundle_pullback_cylinder Q B
  apply cylindrical_translates_complement_precompact T.toHomeomorph D.toHomeomorph h
    (CirclePullback.height_isProperMap B.projection B.projection_continuous) hT
    (fun n => Homeomorph.vadd n) (fun n x => CirclePullback.height_vadd B.projection n x)
    isPreconnected_connectedComponentIn
  intro n
  apply disjoint_left.mpr
  rintro y hy ⟨z, rfl⟩
  have hout := connectedComponentIn_subset
    (q ⁻¹' (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ) a hy
  apply hout
  exact ⟨z, (CirclePullback.projection_vadd B.projection n (D (z, 0))).symm⟩

theorem sphereBundle_cut_component_injective
    (Q : GeneralizedSliceCarrier) [CompactSpace Q.carrier] (B : SurgerySphereBundle Q)
    (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (circlePullbackCarrier Q B.projection B.projection_smooth).carrier ∞)
    (a : (circlePullbackCarrier Q B.projection B.projection_smooth).carrier) :
    let q := circlePullbackProjection Q B.projection B.projection_smooth
    InjOn q (connectedComponentIn
      (q ⁻¹' (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ) a) :=
  CirclePullback.projection_injOn_precompact_component
    B.projection B.projection_continuous _ a (sphereBundle_cut_component_precompact Q B D a)

end PoincareConjecture.M38
