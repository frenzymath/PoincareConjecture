import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open Set Metric unitInterval

namespace ContinuousMap

variable {Y : Type*} [TopologicalSpace Y] [SimplyConnectedSpace Y]

theorem nullhomotopic_addCircle (f : C(UnitAddCircle, Y)) : f.Nullhomotopic := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let p : Path (f 0) (f 0) :=
    { toFun := fun s => f ((s : ℝ) : UnitAddCircle)
      continuous_toFun := f.continuous.comp
        ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)
      source' := by simp
      target' := by
        change f ((1 : ℝ) : UnitAddCircle) = f 0
        rw [AddCircle.coe_period] }
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl (f 0))
  let F : C(I, C(I, Y)) :=
    (H.toHomotopy.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  let F' : C(ℝ, C(I, Y)) := F.IccExtend zero_le_one
  have hF' (s : I) : F' (s : ℝ) = F s :=
    Set.IccExtend_of_mem zero_le_one F s.property
  have hends : F' 0 = F' 1 := by
    change F' ((0 : I) : ℝ) = F' ((1 : I) : ℝ)
    rw [hF', hF']
    ext t
    exact (H.source t).trans (H.target t).symm
  let L : C(UnitAddCircle, C(I, Y)) :=
    ⟨AddCircle.liftIco 1 0 F',
      AddCircle.liftIco_zero_continuous hends F'.continuous.continuousOn⟩
  have hL (s : ℝ) (hs : s ∈ Ico 0 1) (t : I) :
      L (s : UnitAddCircle) t = H (t, ⟨s, hs.1, hs.2.le⟩) := by
    change AddCircle.liftIco 1 0 F' (s : UnitAddCircle) t = _
    rw [AddCircle.liftIco_zero_coe_apply hs]
    exact congrArg (fun g : C(I, Y) => g t) (hF' ⟨s, hs.1, hs.2.le⟩)
  have hrep (x : UnitAddCircle) : ∃ s ∈ Ico (0 : ℝ) 1, (s : UnitAddCircle) = x := by
    have hx : x ∈ ((↑) : ℝ → UnitAddCircle) '' Ico 0 (0 + 1 : ℝ) :=
      (AddCircle.coe_image_Ico_eq (1 : ℝ) 0).symm ▸ mem_univ x
    simpa only [zero_add, mem_image] using hx
  refine ⟨f 0, ⟨{
    toContinuousMap := L.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    obtain ⟨s, hs, rfl⟩ := hrep x
    change L (s : UnitAddCircle) 0 = f (s : UnitAddCircle)
    rw [hL s hs]
    exact H.toHomotopy.apply_zero ⟨s, hs.1, hs.2.le⟩
  · intro x
    obtain ⟨s, hs, rfl⟩ := hrep x
    change L (s : UnitAddCircle) 1 = f 0
    rw [hL s hs]
    exact H.toHomotopy.apply_one ⟨s, hs.1, hs.2.le⟩

theorem nullhomotopic_circle (f : C(Circle, Y)) : f.Nullhomotopic := by
  let e : UnitAddCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let ec : C(UnitAddCircle, Circle) := ⟨e, e.continuous⟩
  let ei : C(Circle, UnitAddCircle) := ⟨e.symm, e.symm.continuous⟩
  have h := (f.comp ec).nullhomotopic_addCircle.comp_left ei
  have he : (f.comp ec).comp ei = f := by
    ext x
    exact congrArg f (e.apply_symm_apply x)
  rwa [he] at h

theorem exists_closedDisk_extension_of_simplyConnected (f : C(Circle, Y)) :
    ∃ g : C(closedBall (0 : ℂ) 1, Y),
      ∀ x : Circle, g ⟨x, sphere_subset_closedBall x.property⟩ = f x :=
  f.nullhomotopic_circle.exists_closedBall_extension f

end ContinuousMap

theorem IsSimplyConnected.exists_circle_extension
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsSimplyConnected U)
    (f : C(Circle, X)) (hf : ∀ x, f x ∈ U) :
    ∃ g : C(closedBall (0 : ℂ) 1, X),
      (∀ x : Circle, g ⟨x, sphere_subset_closedBall x.property⟩ = f x) ∧
      range g ⊆ U ∧ IsCompact (range g) := by
  let : SimplyConnectedSpace U := hU
  let f' : C(Circle, U) := ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk _⟩
  obtain ⟨G, hG⟩ := f'.exists_closedDisk_extension_of_simplyConnected
  let g : C(closedBall (0 : ℂ) 1, X) :=
    ⟨fun x => (G x : X), continuous_subtype_val.comp G.continuous⟩
  refine ⟨g, fun x => congrArg Subtype.val (hG x), ?_, isCompact_range g.continuous⟩
  rintro _ ⟨x, rfl⟩
  exact (G x).property
