import PoincareConjecture.Proofs.M38.EventSlices
import PoincareConjecture.Proofs.M38.FiniteCutComponents
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem neck_central_domain (N : EpsilonNeck g) :
    (Set.univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆
      Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  rintro ⟨z, s⟩ ⟨_, hs⟩
  have hs0 : s = 0 := hs
  subst s
  exact ⟨Set.mem_univ z, neg_neg_of_pos (inv_pos.mpr N.epsilon_pos),
    inv_pos.mpr N.epsilon_pos⟩

theorem neck_central_compact (N : EpsilonNeck g) : IsCompact N.central_sphere := by
  rw [N.central_sphere_eq]
  exact (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
    (N.coordinate_map_smooth.continuousOn.mono (neck_central_domain N))

theorem neck_central_connected (N : EpsilonNeck g) : IsConnected N.central_sphere := by
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  rw [N.central_sphere_eq]
  exact (isConnected_univ.prod isConnected_singleton).image _
    (N.coordinate_map_smooth.continuousOn.mono (neck_central_domain N))

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]

theorem limit_inverse_continuous :
    Continuous (F.event T hT).limit_identify.inverse :=
  continuousOn_univ.mp (F.event T hT).limit_identify.inverse_smooth.continuousOn

theorem limit_inverse_injective :
    Function.Injective (F.event T hT).limit_identify.inverse := by
  intro x y h
  have hx := (F.event T hT).limit_identify.right_inverse (Set.mem_univ x)
  have hy := (F.event T hT).limit_identify.right_inverse (Set.mem_univ y)
  exact hx.symm.trans ((congrArg (F.event T hT).limit_identify.map h).trans hy)

theorem event_sphere_compact (i : Fin (F.event T hT).cap_count) :
    IsCompact ((F.event T hT).limit_identify.inverse ''
      ((F.event T hT).necks i).neck.central_sphere) :=
  (neck_central_compact _).image (limit_inverse_continuous F T hT)

theorem event_sphere_connected (i : Fin (F.event T hT).cap_count) :
    IsConnected ((F.event T hT).limit_identify.inverse ''
      ((F.event T hT).necks i).neck.central_sphere) :=
  (neck_central_connected _).image _ (limit_inverse_continuous F T hT).continuousOn

theorem event_spheres_disjoint (i j : Fin (F.event T hT).cap_count) (hij : i ≠ j) :
    Disjoint ((F.event T hT).limit_identify.inverse ''
      ((F.event T hT).necks i).neck.central_sphere)
      ((F.event T hT).limit_identify.inverse ''
        ((F.event T hT).necks j).neck.central_sphere) := by
  apply (Set.disjoint_image_iff (limit_inverse_injective F T hT)).mpr
  exact ((F.event T hT).neck_carrier_disjoint i j hij).mono
    ((F.event T hT).necks i).neck.central_sphere_subset
    ((F.event T hT).necks j).neck.central_sphere_subset

theorem event_sphere_discarded (i : Fin (F.event T hT).cap_count) :
    (F.event T hT).limit_identify.inverse ''
      ((F.event T hT).necks i).neck.central_sphere ⊆
        (interior (F.event T hT).retained_pre)ᶜ := by
  intro x hx
  have hfrontier : x ∈ frontier (F.event T hT).retained_pre := by
    rw [(F.event T hT).pre_boundary]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  exact hfrontier.2

theorem event_finite_discarded_components :
    Finite (ConnectedComponents {x : (F.slice (F.event T hT).tMinus).carrier //
      x ∉ interior (F.event T hT).retained_pre}) := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let : CompactSpace (F.slice (F.event T hT).tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact _
      (mem_time_domain_before_surgery F hT (F.event T hT).tMinus_nonnegative
        (F.event T hT).tMinus_lt.le))
  apply finite_components_of_frontier_cover isOpen_interior.isClosed_compl
    (fun i => (F.event T hT).limit_identify.inverse ''
      ((F.event T hT).necks i).neck.central_sphere)
    (event_sphere_connected F T hT) (event_sphere_discarded F T hT)
  rw [frontier_compl, ← (F.event T hT).pre_boundary]
  exact frontier_interior_subset

end PoincareConjecture.M38
